{
  inputs = {
    nixpkgs.url = "nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    nix-filter.url = "github:numtide/nix-filter";

    fenix = {
      url = "github:nix-community/fenix";
      inputs.nixpkgs.follows = "nixpkgs";
    };

    naersk = {
      url = "github:nix-community/naersk";
      inputs.nixpkgs.follows = "nixpkgs";
    };
  };

  outputs = {
    self,
    fenix,
    flake-utils,
    naersk,
    nix-filter,
    nixpkgs,
  }:
    flake-utils.lib.eachDefaultSystem (system: let
      overlays = [fenix.overlays.default];
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
          dir = ./rr_frontend;
          sha256 = "sha256-0NR5RJ4nNCMl9ZQDA6eGAyrDWS8fB28xIIS1QGLlOxw=";
        };

        env = naersk.lib.${system}.override {
          cargo = rust.toolchain;
          rustc = rust.toolchain;
        };
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

            src = with nix-filter.lib;
              nix-filter {
                root = ./.;
                include = ["dune-project" (inDirectory "theories")];
              };

            propagatedBuildInputs = with coq.pkgs; [coq-record-update equations lambda-rust];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };

        frontend = rust.env.buildPackage rec {
          inherit meta version;

          pname = "cargo-${name}";
          src = ./rr_frontend;

          buildInputs = [rust.toolchain];
          nativeBuildInputs = with pkgs;
            [makeWrapper pkgs.gnupatch]
            ++ lib.optionals stdenv.isDarwin [libzip];

          postInstall = with pkgs.lib.strings; ''
            wrapProgram $out/bin/refinedrust-rustc \
              --set LD_LIBRARY_PATH "${rust.lib}"

            wrapProgram $out/bin/${pname} \
              --set PATH "${makeSearchPath "bin" buildInputs}"
          '';
        };

        default = pkgs.buildEnv {
          inherit meta;

          name = "cargo-${name}";
          paths = coq.toolchain ++ [packages.frontend rust.toolchain];

          pathsToLink = ["/bin"];
          nativeBuildInputs = [pkgs.makeWrapper pkgs.gnupatch];
          postBuild = with pkgs.lib.strings; ''
            wrapProgram $out/bin/dune \
              --set COQPATH "${makeSearchPath "lib/coq/${coq.version}/user-contrib" (fetchCoqDeps packages.theories)}"
          '';
        };
      };

      devShells.default = pkgs.mkShell {
        inputsFrom = with packages; [frontend theories];

        shellHook = ''
          export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH}:${rust.lib}
          export RUST_SRC_PATH=${rust.src}/rustc_driver/Cargo.toml
        '';
      };

      formatter = pkgs.alejandra;
    });
}
