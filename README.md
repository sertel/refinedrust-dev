# RefinedRust verification framework

This repository contains a public mirror of the RefinedRust development version.

## Structure
The Coq implementation of RefinedRust can be found in the `theories` subfolder.
The frontend implementation can be found in the `rr_frontend` subfolder.
Case studies and tests can be found in the `case_studies` subfolder.
Stdlib interfaces (without proofs) can be found in the `stdlib` subfolder.

The file `paper_mapping.md` in this repository contains more details on how to map the contents of the RefinedRust paper to this repository.

### For the `theories` subfolder:
* the `caesium` subfolder contains the Radium operational semantics, an adaptation of RefinedC's Caesium semantics.
* the `lithium` subfolder contains RefinedC's Lithium separation logic automation engine with very lightweight modifications.
* the `rust_typing` subfolder contains the implementation of the RefinedRust type system and proof automation.

## Setup
To use this project, you will need to install some specific dependencies.

There are two maintained ways to do this, using `nix` or (`opam` and `rustup`).

If you are using `nix`, you do not need to have a copy of this repository.

### Setup using `nix` flakes
We assume that you have `nix` installed on your system. Setup instructions can be found here: https://nixos.org/download

You can use `nix shell` to enter an interactive subshell containing the project:
```bash
nix shell "gitlab:lgaeher/refinedrust-dev?host=gitlab.mpi-sws.org"
```

The project lives in this subshell and will disappear as soon as you leave the subshell.

If you do not have flakes enabled, you may get this error:
```
error: experimental Nix feature 'nix-command' is disabled; use ''–extra-experimental-features nix-command' to override
```

All you have to do is activate flakes temporarily by using `--extra-experimental-features 'nix-command flakes'`:
```bash
nix --extra-experimental-features 'nix-command flakes' shell "gitlab:lgaeher/refinedrust-dev?host=gitlab.mpi-sws.org"
```

### Setup using `opam` and `rustup`
#### Setup instructions for the Coq code:
We assume that you have `opam` installed on your system. Setup instructions can be found here: https://opam.ocaml.org/doc/Install.html

0. `cd` into the directory containing this README.

1. Create a new opam switch for RefinedRust:
```
opam switch create refinedrust --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda
opam switch link refinedrust .
opam switch refinedrust
opam repo add coq-released https://coq.inria.fr/opam/released
opam repo add iris-dev https://gitlab.mpi-sws.org/iris/opam.git
```
2. Install the necessary dependencies:
```
opam pin add coq 8.17.1
opam pin add coq-lambda-rust.dev https://gitlab.mpi-sws.org/lgaeher/lambda-rust.git#rr
make builddep
```
3. Build the project
```
dune build theories
```

#### Setup instructions for the frontend:
1. Make sure that you have a working `rustup`/Rust install. Instructions for setting up Rust can be found on https://rustup.rs/.
   Note that Rust packages shipped via many package managers are not compatible, as RefinedRust depends on being able to install a specific version of Rust using `rustup`.
   You can check if your install is okay by running `rustup show`. If this command succeeds, you should be good to go.
   Otherwise, remove your existing Rust install and install it via https://rustup.rs/.
2. Run `./refinedrust build` in `rr_frontend` to build the frontend.
3. Run `./refinedrust install` in `rr_frontend` to install the frontend.

The last command will install RefinedRust's frontend into Rustup's install directory.

## Frontend usage
After installing RefinedRust, it can be invoked through `cargo`, Rust's build system and package manager, by running `cargo refinedrust`.

For example, you can build the examples from the paper (located in `case_studies/paper-examples`) by running:
```
cd case_studies/paper-examples
cargo refinedrust
dune build
```

The invocation of `cargo refinedrust` will generate a folder `output/paper_examples` with two subdirectories: `generated` and `proofs`.
The `generated` subdirectory contains auto-generated code that may be overwritten by RefinedRust at any time during subsequent invocations.
The `proofs` subdirectory contains proofs which may be edited manually (see the section [Proof Editing](#proof-editing) below) and are not overwritten by RefinedRust.

More specifically, the `generated` directory will contain:
* `generated_code_crate.v` contains the definition of the code translated to the Radium semantics, including layout specifications for the used structs and enums.
* `generated_specs_crate.v` contains the definition of the annotated specifications for functions and data structures in terms of RefinedRust's type system.
* for each function `fun` with annotated specifications: a file `generated_template_fun.v` containing the lemma statement that has to be proven to show the specification, as well as auto-generated parts of the proof that may change when implementation details of `fun` are changed.

The `proofs` subdirectory contains for each function `fun` a proof that invokes the components defined in the `generated_template_fun.v` file.

In addition, RefinedRust generates an `interface.rrlib` file containing the ADTs and functions which are publicly exported and specified.
Verification of other crates can import these specifications.
The `lib_load_paths` config option influences where the verifier searches for these interface files.
The crate-level `rr::include` directive can be used to import these proof files (see the description in `SPEC_FORMAT.md`).

## Proof editing
In order to interactively look at the generated code using a Coq plugin like Coqtail, VSCoq, or Proof General for the editor of your choice, you need to add a line pointing to the directory of the generated code in the `_CoqProject` file.
See the existing includes for inspiration.

Changes to the `proof_*.v` files in the generated `proofs` folder are persistent and files are not changed once RefinedRust has generated them once.
This enables to write semi-automatic proofs.
`proof_*.v` files are intended to be checked into `git`, as they are stable.

On changes to implementations or specifications, only the files located in `generated` are modified.
The default automatic proofs in `proof_*.v` files are stable under any changes to a function.
Of course, once you change proofs manually, changing an implementation or specification may require changes to your manually-written code.

## Frontend Configuration
Configuration options can be set in the `RefinedRust.toml` file.
These include:

| Option | Type | Configures |
|--------|------|------------|
| `work_dir` | Relative/absolue path | Determines the working directory. Other relative paths are interpreted relative to this one. |
| `dump_borrowck_info` | Boolean | Dumps borrowck debug output in the log directory |
| `output_dir` | Relative/absolute path | Determines the directory where the generated output files will be placed |
| `log_dir` | Relative/absolute path | Determines the directory where logs and debug dumps will be placed if enabled |
| `shims` | Relative/absolute path | Determines the JSON file storing information about shims that RefinedRust uses |
| `run_check` | Boolean | Automatically call the Coq type checker on the generated files |
| `verify_deps` | Boolean | Verify dependencies or not |
| `admit_proofs` | Boolean | Skip Coq's `Qed` check and instead run `Admitted` |
| `extra_specs` | Relative/absolute path | File whose contents will be inlined at the end of the generated specs file |
| `post_generation_hook` | Command | Run a command after code generation and before proof checking |
| `lib_load_paths` | Array of relative/absolute paths to directories | Search these paths (recursively) for RefinedRust libraries |

The path to the config file can also be specified via the environment variable `RR_CONFIG`.
Setting this variable will also change the `work_dir` (relative to which paths are interpreted) to the path of `RR_CONFIG`.

Overrides for all settings can be specified in the environment via variables with the prefix `RR_`, e.g. `RR_SHIMS`, `RR_DUMP_BORROWCK_INFO`, etc.

## License
We currently re-use code from the following projects:
- rustc: https://github.com/rust-lang/rust (under the MIT license)
- miri: https://github.com/rust-lang/miri (under the MIT license)
- RefinedC: https://gitlab.mpi-sws.org/iris/refinedc (under the BSD 3-clause license)
- Iris: https://gitlab.mpi-sws.org/iris/iris (under the BSD 3-clause license)
- lambda-rust: https://gitlab.mpi-sws.org/iris/lambda-rust (under the BSD 3-clause license)
- Prusti: https://github.com/viperproject/prusti-dev (under the MPL 2.0 license)
- Coq ident-to-string: https://github.com/mit-plv/coqutil/blob/master/src/coqutil/Macros/ident_to_string.v (under the MIT license)

We provide the RefinedRust code under the BSD 3-clause license.
