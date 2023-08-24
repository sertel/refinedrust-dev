# RefinedRust verification framework

This repository contains a public mirror of the RefinedRust development version.
Currently, this does include the Coq source code of the type system. We will publish the implementation of the type system soon.

## Structure
The Coq implementation of RefinedRust can be found in the `theories` subfolder.
The frontend implementation and examples can be found in the `rr_frontend` subfolder.

### For the `theories` subfolder:
* the `caesium` subfolder contains the Radium operational semantics, an adaptation of RefinedC's Caesium semantics.
* the `lithium` subfolder contains RefinedC's Lithium separation logic automation engine with very lightweight modifications.


### For the `rr_frontend` subfolder:

### Structure of the generated code:
For each input module `mod`, the RefinedRust generates the following files in the corresponding output directory:
* `generated_code_mod.v` contains the definition of the code translated to the Radium semantics, including layout specifications for the used structs and enums.
* `generated_specs_mod.v` contains the definition of the annotated specifications for functions and data structures in terms of RefinedRust's type system.
* `extra_proofs_mod.v` allows users to add custom theory for use in specifications and proofs.
* for each function `fun` with annotated specifications: a file `generated_proof_fun.v` containing the automatically-generated typing proof that calls into RefinedRust's automation.

## Setup
### Setup instructions for the Coq code:
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
opam pin add coq 8.17.0
opam pin add coq-lambda-rust.dev https://gitlab.mpi-sws.org/lgaeher/lambda-rust.git
make builddep
```
3. Build the project
```
dune build
```


### Setup instructions for the frontend:
1. Make sure that you have a working `rustup`/Rust install. Instructions for setting up Rust can be found on https://rustup.rs/.
2. Run `cargo install rustup-toolchain-install-master`.
3. Run `./rustup-toolchain` in `rr_frontend` to setup a Rust toolchain called `refinedrust`.
4. Run `./refinedrust build` in `rr_frontend` to build the frontend.


## Frontend usage
To use RefinedRust's frontend to generate the Coq input for RefinedRust's type system, switch to the `rr-frontend` directory.
Then, assuming you want to translate `path-to-file.rs`, run:
```
./refinedrust run -- path-to-file.rs
```
For example:
```
./refinedrust run -- examples/paper.rs
```
This will create a new directory called `section2` in the `output` folder.

To then compile the generated Coq code, switch to `output/paper` and run `dune build`.

In order to interactively look at the generated code using a Coq plugin like Coqtail, VSCoq, or Proof General for the editor of your choice, you need to add a line pointing to the directory of the generated code in the `_CoqProject` file.
See the existing includes for inspiration.

## Frontend Configuration
Configuration options can be set in the `RefinedRust.toml` file.
These include:

| Option | Type | Configures |
|--------|------|------------|
| `dump_borrowck_info` | Boolean | Dumps borrowck debug output in the log directory |
| `output_dir` | Relative path | Determines the directory where the generated output files will be placed |
| `log_dir` | Relative path | Determines the directory where logs and debug dumps will be placed if enabled |
| `shims` | Relative path | Determines the JSON file storing information about shims that RefinedRust uses |
| `run_check` | Boolean | Automatically call the Coq type checker on the generated files |



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
