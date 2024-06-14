{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-23.11";
    flake-utils.url = "github:numtide/flake-utils";

    crane = {
      url = "github:ipetkov/crane";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    crane,
    fenix,
    flake-utils,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      ocamlFlambda = _: prev: rec {
        ocamlPackages_4_14 = prev.ocamlPackages.overrideScope' (_: prev: {
          ocaml = prev.ocaml.override {flambdaSupport = true;};
        });
        coqPackages_8_17 = prev.coqPackages_8_17.overrideScope' (_: prev: {
          coq = prev.coq.override {
            ocamlPackages_4_14 = ocamlPackages_4_14;
          };
        });
      };
      overlays = [fenix.overlays.default ocamlFlambda];
      pkgs = import nixpkgs {inherit overlays system;};

      name = "refinedrust";
      version = "0.1.0";

      coq = {
        pkgs = pkgs.coqPackages_8_17;
        toolchain = [coq.pkgs.coq] ++ coq.pkgs.coq.nativeBuildInputs;
        version = coq.pkgs.coq.coq-version;

        stdpp = {
          version = "4be5fd62ddbd5359f912e2cebb415b015c37e565";
          sha256 = "sha256-9pNWjPy1l1EovcKZchC/23FwlllD/Oa3jEOtN5tDzik=";
        };

        iris = {
          version = "1de1b3112754e14a4968534572e118a23344eafe";
          sha256 = "sha256-Cimb3XxnchPSWVGMSyWmJdLQqHMilw11o2hq/4h8dVQ=";
        };

        lambda-rust = {
          version = "4ec2733cce240e3595c37cb926eb000455be77a4";
          sha256 = "sha256-kX9NIPPOoajuJDVly9qGUCCd3lt8Da2k0dZnDY2zKbY=";
        };
      };

      meta = with pkgs.lib; {
        homepage = "https://gitlab.mpi-sws.org/lgaeher/refinedrust-dev";
        license = licenses.bsd3;
      };

      rust = {
        toolchain = pkgs.fenix.fromToolchainFile {
          file = ./rust-toolchain.toml;
          sha256 = "sha256-0NR5RJ4nNCMl9ZQDA6eGAyrDWS8fB28xIIS1QGLlOxw=";
        };

        env = let
          cargo-bindeps = pkgs.symlinkJoin {
            name = "cargo-bindeps";
            paths = [pkgs.cargo];
            nativeBuildInputs = [pkgs.makeWrapper];
            postBuild = ''
              wrapProgram $out/bin/cargo \
                --add-flags "-Zbindeps"
            '';
          };

          craneLib = (crane.mkLib pkgs).overrideScope (_: prev: {
            downloadCargoPackageFromGit = prev.downloadCargoPackageFromGit.override (args: {
              pkgsBuildBuild = args.pkgsBuildBuild // {cargo = cargo-bindeps;};
            });
          });
        in
          craneLib.overrideToolchain rust.toolchain;

        lib = "${rust.toolchain}/lib/rustlib/$(rustc -Vv | grep '^host:' | cut -d' ' -f2)/lib";
        src = "${rust.toolchain}/lib/rustlib/rustc-src/rust/compiler";
      };
    in rec {
      packages = let
        fetchCoqDeps = with pkgs.lib;
          drv: [drv] ++ flatten (map fetchCoqDeps drv.propagatedBuildInputs);

        mkDepCoqDerivation = pin: {
          pname,
          propagatedBuildInputs ? [],
          owner ? "iris",
        }:
          coq.pkgs.mkCoqDerivation {
            inherit pname propagatedBuildInputs owner;

            domain = "gitlab.mpi-sws.org";
            preBuild = "patchShebangs coq-lint.sh";

            release.${pin.version}.sha256 = "${pin.sha256}";
            version = pin.version;
          };
      in {
        theories = let
          stdpp = mkDepCoqDerivation coq.stdpp {
            pname = "stdpp";
          };

          iris = mkDepCoqDerivation coq.iris {
            pname = "iris";

            propagatedBuildInputs = [stdpp];
          };

          lambda-rust = mkDepCoqDerivation coq.lambda-rust {
            pname = "lambda-rust";
            owner = "lgaeher";

            propagatedBuildInputs = [iris];
          };
        in
          coq.pkgs.mkCoqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;

            src = ./theories;

            propagatedBuildInputs = with coq.pkgs; [coq-record-update equations lambda-rust];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };

        frontend = let
          src = ./rr_frontend;
          pname = "cargo-${name}";

          cargoArtifacts = rust.env.buildDepsOnly {
            inherit meta pname src version;
          };
        in
          rust.env.buildPackage rec {
            inherit cargoArtifacts meta pname src version;

            buildInputs = [rust.toolchain pkgs.gnupatch];
            nativeBuildInputs = with pkgs;
              [makeWrapper]
              ++ lib.optionals stdenv.isDarwin [libzip libiconv];

            postInstall = with pkgs.lib.strings; ''
              wrapProgram $out/bin/refinedrust-rustc \
                --set LD_LIBRARY_PATH "${rust.lib}" \
                --set DYLD_FALLBACK_LIBRARY_PATH "${rust.lib}"

              wrapProgram $out/bin/${pname} \
                --set PATH "${makeSearchPath "bin" buildInputs}"
            '';

            doCheck = false;
          };

        stdlib = coq.pkgs.mkCoqDerivation {
          inherit meta version;

          pname = "refinedrust-stdlib";
          opam-name = "refinedrust-stdlib";
          src = ./stdlib;

          buildInputs = [packages.frontend rust.toolchain];
          propagatedBuildInputs = [packages.theories];

          preBuild = ''
            dune() { command dune $@ --display=short; }
            make generate_stdlib
          '';
          useDune = true;
        };

        default = pkgs.buildEnv {
          inherit meta;

          name = "cargo-${name}";
          paths = coq.toolchain ++ [packages.frontend rust.toolchain];

          pathsToLink = ["/bin"];
          nativeBuildInputs = [pkgs.makeWrapper];
          postBuild = with pkgs.lib.strings; ''
            wrapProgram $out/bin/dune \
              --set COQPATH "${makeSearchPath "lib/coq/${coq.version}/user-contrib" (fetchCoqDeps packages.stdlib)}"
          '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend theories];

        packages = with pkgs; [gnumake gnupatch gnused];

        shellHook = ''
          export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH}:${rust.lib}
          export DYLD_FALLBACK_LIBRARY_PATH=''${DYLD_FALLBACK_LIBRARY_PATH}:${rust.lib}
          export RUST_SRC_PATH=${rust.src}/rustc_driver/Cargo.toml
        '';
      };

      formatter = pkgs.alejandra;
    });
}
