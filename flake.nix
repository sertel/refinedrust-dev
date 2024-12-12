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
  }: let
        mkDepCoqDerivation = pin :
          { lib,
            mkCoqDerivation,
            pname,
            propagatedBuildInputs ? [],
            owner ? "iris",
          }:
          mkCoqDerivation {
            inherit pname propagatedBuildInputs owner;

            domain = "gitlab.mpi-sws.org";
            preBuild = "patchShebangs coq-lint.sh";

            version = pin.version;
            release.${pin.version} = {
              src = lib.const (lib.cleanSourceWith {
                src = lib.cleanSource ./.;
                filter = let inherit (lib) hasSuffix; in path: type:
                  (! hasSuffix ".gitignore" path)
                  && (! hasSuffix "flake.nix" path)
                  && (! hasSuffix "flake.lock" path)
                  && (! hasSuffix "_build" path);
              });
              sha256 = "${pin.sha256}";
            };
          };

        stdpp-fun = { lib, mkCoqDerivation, coq }:
          mkDepCoqDerivation coq.stdpp {
            inherit lib mkCoqDerivation;

            pname = "stdpp";
          };

        iris-fun = { lib, mkCoqDerivation, coq, stdpp } :
          mkDepCoqDerivation coq.iris {
            inherit lib mkCoqDerivation;

            pname = "iris";

            propagatedBuildInputs = [stdpp];
          };

        lambda-rust-fun = { lib, mkCoqDerivation, coq, iris }:
          mkDepCoqDerivation coq.lambda-rust {
            inherit lib mkCoqDerivation;

            pname = "lambda-rust";
            owner = "lgaeher";

            propagatedBuildInputs = [iris];
          };

        theories-fun = { lib, meta, version, name, mkCoqDerivation, coq, coq-record-update, equations, lambda-rust }:
          mkCoqDerivation {
            inherit meta version;

            pname = name;
            opam-name = name;

            src = ./theories;

            propagatedBuildInputs = with coq.pkgs; [coq-record-update equations lambda-rust];

            preBuild = "dune() { command dune $@ --display=short; }";
            useDune = true;
          };

         stdlib-fun = { lib, meta, version, rust, mkCoqDerivation, frontend, theories }:
           mkCoqDerivation {
             inherit meta version;

             pname = "refinedrust-stdlib";
             opam-name = "refinedrust-stdlib";
             src = ./stdlib;

             buildInputs = [frontend rust.toolchain];
             propagatedBuildInputs = [theories];

             preBuild = ''
                      dune() { command dune $@ --display=short; }
                      make generate_stdlib
                '';
             useDune = true;
           };

         frontend-fun = { lib, meta, version, name, makeWrapper, stdenv, libzip, libiconv, rust, gnupatch }:
           let
             src = ./rr_frontend;
             pname = "cargo-${name}";

             cargoArtifacts = rust.env.buildDepsOnly {
               inherit meta pname src version;
             };
           in
             rust.env.buildPackage rec {
               inherit cargoArtifacts meta pname src version;

               buildInputs = [rust.toolchain gnupatch];
               nativeBuildInputs =
                 [makeWrapper]
                 ++ lib.optionals stdenv.isDarwin [libzip libiconv];

               postInstall = with lib.strings; ''
                wrapProgram $out/bin/refinedrust-rustc \
                  --set LD_LIBRARY_PATH "${rust.lib}" \
                  --set DYLD_FALLBACK_LIBRARY_PATH "${rust.lib}"

                wrapProgram $out/bin/${pname} \
                  --set PATH "${makeSearchPath "bin" buildInputs}"
                '';

               doCheck = false;
             };

         default-fun = { pkgs, meta, name, coq, rust, fetchCoqDeps, frontend, stdlib }: pkgs.buildEnv {
           inherit meta;

           name = "cargo-${name}";
           paths = coq.toolchain ++ [frontend rust.toolchain];

           pathsToLink = ["/bin"];
           nativeBuildInputs = [pkgs.makeWrapper];
           postBuild = with pkgs.lib.strings; ''
                       wrapProgram $out/bin/dune \
                       --set COQPATH "${makeSearchPath "lib/coq/${coq.version}/user-contrib" (fetchCoqDeps stdlib)}"
                       '';
         };

         config-fun = pkgs :
           rec {
             fetchCoqDeps = with pkgs.lib;
                drv: [drv] ++ flatten (map fetchCoqDeps drv.propagatedBuildInputs);

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

                env =
                  let
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
           };
  in {
      # NOTE: To use this flake, apply the following overlay to nixpkgs and use
      # the injected package from its respective coqPackages_VER attribute set!
      overlays.default = final: prev:
        let
          pkgs = prev;
          config = config-fun pkgs;
          injectPkg = name: set:
            prev.${name}.overrideScope (self: _: {
              # FIXME this should really have a better name such as rr.theories and rr.frontend
              stdpp       = self.callPackage stdpp-fun       { inherit (config) coq; };
              iris        = self.callPackage iris-fun        { inherit (config) coq; };
              lambda-rust = self.callPackage lambda-rust-fun { inherit (config) coq; };
              theories    = self.callPackage theories-fun    { inherit (config) coq meta version name; };
              stdlib      = self.callPackage stdlib-fun      { inherit (config) meta version rust; };
              frontend    = self.callPackage frontend-fun    { inherit (config) meta version name rust; };
              def         = self.callPackage default-fun     { inherit (config) coq meta name rust fetchCoqDeps; };
            });
        in (nixpkgs.lib.mapAttrs injectPkg {
          inherit (final) coqPackages_8_17;
        });
    }
  //
    flake-utils.lib.eachDefaultSystem (system:
      let
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

        overlays = [
          fenix.overlays.default
          ocamlFlambda
          self.overlays.default
        ];

        pkgs = import nixpkgs {inherit overlays system;};

        packages = {
#          stdpp       = pkgs.coqPackages_8_17.stdpp;
#          iris        = pkgs.coqPackages_8_17.iris;
#          lambda-rust = pkgs.coqPackages_8_17.lambda-rust;
          theories    = pkgs.coqPackages_8_17.theories;
          frontend    = pkgs.coqPackages_8_17.frontend;
          stdlib      = pkgs.coqPackages_8_17.stdlib;
          def         = pkgs.coqPackages_8_17.def;

          default  = self.packages.${system}.def;
         };

         config = config-fun pkgs;

         devShells.default = pkgs.mkShell {
           inputsFrom = with packages; [frontend theories];

           packages = with pkgs; [gnumake gnupatch gnused];

           shellHook = ''
             export LD_LIBRARY_PATH=''${LD_LIBRARY_PATH}:${config.rust.lib}
             export DYLD_FALLBACK_LIBRARY_PATH=''${DYLD_FALLBACK_LIBRARY_PATH}:${config.rust.lib}
             export RUST_SRC_PATH=${config.rust.src}/rustc_driver/Cargo.toml
           '';
         };
       in {
         inherit packages devShells;
         formatter = pkgs.alejandra;
       });
}
