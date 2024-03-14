# Mapping from the paper to the implementation

This document describes how to map the concepts and results from the paper to the implementation.

## Structure
The Coq implementation of RefinedRust can be found in the `theories` subfolder.
The frontend implementation can be found in the `rr_frontend` subfolder.
Case studies and tests can be found in the `case_studies` subfolder.

### For the `theories` subfolder:
* the `caesium` subfolder contains the Radium operational semantics, an adaptation of RefinedC's Caesium semantics.
* the `lithium` subfolder contains RefinedC's Lithium separation logic automation engine with very lightweight modifications.
* the `rust_typing` subfolder contains the implementation of the RefinedRust type system and proof automation.

### For the `case_studies` subfolder:
Each subfolder is a Cargo crate (i.e. a Rust project).
* the `paper_examples` folder contains the smaller examples from the paper from Sections 2 and 5
* the `minivec` folder contains the vector implementation we have verified
* the `tests` folder contains some smaller test cases

## General remarks
The specification language has been updated slightly since the submission of the paper:
* In pre-/postconditions (`rr::requires` and `rr::ensures`) and invariants (`rr::invariant`), propositions are by default interpreted as pure Coq propositions, removing the need for `⌜ ... ⌝` brackets.
  In exchange, for writing an Iris proposition like `"Obs γ x"`, we have to write `#iris "Obs γ x"` instead.
* We introduced syntactic sugar for writing observations. Instead of `rr::ensures("Obs γ x")`, we now write `rr::observe("γ": "x")`.

Moreover, there are some notable differences in terminology and notations:
* In the paper, we use "mathematical types" to denote the mathematical model of a type (e.g. "Z" is the mathematical type of "int i32").
  In our implementation, we call this a "refinement type".
  Correspondingly, instead of the "{math_type T}" notation, the RefinedRust frontend uses "{rt_of T}" (where "rt" is short for "refinement type"), and instead of using the metavariable `τ` to denote refinement types, we use `rt`.
* Instead of `*γ` for embedding a borrow variable `γ` into `bor τ` (described in Section 2.3), we write `👻 γ` or `PlaceGhost γ`.
* Place types are called `ltype`s in Coq, where the `l` is for "location", alluding to `lvalues` in C terminology.
* The typechecking procedures in Section 5 are only loosely implemented like that in our Coq formalization.
  Technically, the procedures are implemented as a separation logic goal where the sequencing of goals in the procedure is given by joining the different goals with separating conjunctions from left to right.
  Some judgments (like `typecheck-mut-bor`, Figure 9) which directly relate to the syntax of the program are implemented as primitive procedures in the RefinedRust automation tactics which are directly applied.
  Other judgments (like `typecheck-place-access`, Figure 10) which depend on some current type assignment and branch depending on the type are implemented as Coq type classes and different branches are implemented as instances of that typeclass. Lithium will find the appropriate instances to apply.
  The Coq implementation for the procedures mentioned in the paper contains comments explaining this in more detail.

At submission time, there are some bugs in how the RefinedRust frontend generates lifetime annotations that guide the RefinedRust type system.
For that reason, we need to patch the the generated code for the `minivec` case study.
The patch can be found in `case_studies/minivec/annotation_patch.patch`; it is automatically applied by RefinedRust's config when regenerating the code.
The lifetime annotations are only there for guiding the type system, but are not relevant for soundness.

## Mapping to the code

### Rust example code
The examples in the paper can be found in the following locations, relative to the `case_studies` folder in the root of this repository:

| Example             | Rust name        | Rust location                 | Remarks |
|---------------------|------------------|-------------------------------|---------|
| Fig. 1              | `box_add_42`       | `paper-examples/src/main.rs`    |         |
| Fig. 2              | `mut_ref_add_42`   | `paper-examples/src/main.rs`    |         |
| Example in Sec 2.2  | `mut_ref_add_client` | `paper-examples/src/main.rs` |         |
| Fig. 3              | `get_mut_client`   | `minivec/src/client.rs`         | desugared because the `vec!` macro is not supported |
| Fig. 3              | `Vec::get_mut`     | `minivec/src/lib.rs`            |         |
| Fig. 3              | `Vec::get_unchecked_mut` | `minivec/src/lib.rs`  |         |
| Fig. 4              | `RawVec`                  | `minivec/src/lib.rs`                               |         |
| Fig. 4              | `Vec`                  | `minivec/src/lib.rs`                               |         |
| Fig. 5              | `Vec::get_unchecked_mut` | `minivec/src/lib.rs` | |
| Fig. 8              | `assert_pair` | `paper-examples/src/main.rs` | |

### Coq formalization
The mathematical/Coq concepts can be found as follows, where paths are relative to the `theories` folder:

#### Section 2
- `bor τ` (Sec 2.3) is called `place_rfn` in and is located in `rust_typing/ltypes.v`.
- the `#x` notation (Sec 2.3) is `#x` in Coq and called `PlaceIn x`, defined in `rust_typing/ltypes.v`.
- the `*γ` notation (Sec 2.3) is `👻 γ` in Coq and called `PlaceGhost γ`, defined in `rust_typing/ltypes.v`

#### Section 4
The parameterization over layout algorithms described in Section 4 is implemented as follows:
+ Next to Caesium's existing notion of `layout` (`caesium/layout.v`), which describes a concrete size and alignment, we add a notion of "syntactic types" `syntype` (`caesium/syntypes.v`) which describe an abstract data layout.
For instance, `IntSynType i32` is the syntactic type of 32-bit integers, and `StructSynType "MyStruct" [("field1", IntSynType i32)]` describes the syntactic type of a struct containing one field `field1` of 32-bit integers.
+ We can compute a layout for every syntactic type using the `use_layout_alg : syntype -> option layout` (`caesium/syntypes.v`) procedure. For syntactic types with a fixed representation (like 32-bit integers), this will compute the canonical layout, while for structs, it will first recursively compute the layout of all fields and then call a specialized struct layout algorithm `struct_layout_alg` for computing the final layout of the struct, including padding.
+ The concrete algorithm to use for `struct_layout_alg` is a parameter of our verification, encapsulated by the `LayoutAlg` typeclass (`caesium/syntypes.v`).
+ In order to handle generic arguments, we parameterize the generated code by the syntactic type of the generic arguments, and assume for the verification that `use_layout_alg` can compute some (unknown) concrete layout for the generic argument. For any concrete program, all generic arguments will be instantiated at link time (as the Rust compiler monomorphizes all functions), and so these assumptions have to be resolved using the concrete chosen layout algorithm at link time.

#### Section 5.1
- RefinedRust's notion of value types are formalized directly using their semantic interpretation. A value type is a `type` in RefinedRust, formalized in `rust_typing/type.v`.
- The value types in Figure 6 are implemented as follows:
  + `int it` can be found as `int it` in `rust_typing/int.v`
  + `bool` can be found as `bool_t` in `rust_typing/int.v`
  + `&mut T` can be found as `mut_ref` in `rust_typing/references.v`
  + `&shr T` can be found as `shr_ref` in `rust_typing/references.v`
  + `box T` can be found as `box` in `rust_typing/box.v`
  + `*mut T` can be found as `alias_ptr_t` in `rust_typing/alias_ptr.v`
  + `struct sl Ts` can be found as `struct_t ` in `rust_typing/products.v`
  + `array n T` can be found as `array_t` in `rust_typing/arrays.v`
  + `uninit` can be found as `uninit` in `rust_typing/uninit_def.v`
  + `maybe_init T` can be found as `maybe_uninit` in `rust_typing/maybe_uninit.v`
  + `abstract E T` can be found as `ex_plain_t` in `rust_typing/existentials.v`. The record describing the abstraction is called `ex_inv_def`.

#### Section 5.2
- RefinedRust's notion of place types is called `ltype` in Coq and is formalized by giving a closed set of place types. The definition can be found in `rust_typing/ltypes.v`.
- The place types in Figure 7 are implemented as follows (all can be found in `rust_typing/ltypes.v`):
  + `place T` is called `OfTy`, as it converts a value type into a place type. We use the notation `◁ T` for it.
  + `&mut p` is called `MutLtype`
  + `&shr p` is called `ShrLtype`
  + `box p` is called `BoxLtype`
  + `struct sl ps` is called `StructLtype`
  + `array n T` is called `ArrayLtype`
  + `blocked T` is called `BlockedLtype`
  + `yoinked pfull pcur` is called `OpenedLtype`. It takes additional parameters compared to the simplified presentation in the paper, which are explained in the comments on its definition.
- The unfolding laws for place types mentioned in 5.2 are located in the files of their corresponding value types. For instance, for mutable references, this is `mut_ref_unfold` in `rust_typing/references.v`, and for structs it is `struct_t_unfold` in `rust_typing/products.v`.

#### Section 5.3
- The procedure for checking mutable borrows in Figure 9 is split across various different judgments.
  The entry point is the `type_borrow_mut` rule in `rust_typing/program_rules.v`.
  After the stratification step in line 6, the rest of the procedure is handled by the `typed_borrow_mut_end` judgment (`rust_typing/programs.v`) and its rule `type_borrow_mut_end` (in `rust_typing/program_rules.v`).
- The procedure for checking place accesses in Figure 10 is handled by the `typed_place` judgment (`rust_typing/programs.v`). The procedure shown in the paper and in particular the case analysis on the place access in the current type is implemented through several different rules for this judgment that are used by Lithium depending on which arguments `typed_place` is called with.
  Some of these instances are located in `rust_typing/program_rules.v`, while others are in the files corresponding to individual place types (e.g. `rust_typing/references.v` for place accesses to reference types).
  For instance, the instance responsible for resolving borrows (line 4) is called `typed_place_resolve_ghost` (`rust_typing/program_rules.v`), while the instances for accessing fields of a struct are located in `rust_typing/products.v`, e.g. `typed_place_struct_owned`.
- The procedure for reading from a place in Figure 11 is split across various different judgments.
  The entry point is the `type_read` rule in `rust_typing/program_rules.v`.
  After the stratification step in line 6, the rest of the procedure is handled by the `typed_read_end` judgment (`rust_typing/programs.v`), which has different rules for the case that the read type is Copy or not.
  The rule for the case that the type is Copy is `type_read_ofty_copy` (`rust_typing/program_rules.v`).

#### Section 5.4
- Our extension of the lifetime logic with Pinned Borrows is implemented and explained in `rust_typing/pinned_borrows.v`.
- The adequacy theorem can be found in `rust_typing/adequacy.v`, lemma `refinedrust_adequacy`.

#### Section 6
- The mentioned shims for pointer manipulation and allocation can be found in `rust_typing/shims.v`.
- The evaluation metrics have been measured in the following way:
  + The size of the source code of the vector implementation has been measured with `tokei` (https://github.com/XAMPPRocky/tokei).
    For measuring the size of the Rust code itself, we have removed all annotations and all extra function wrappers from the file and then called `tokei case_studies/minivec/src/lib.rs`.
    For measuring the size of the annotations, we have added back the annotations and again called `tokei case_studies/minivec/src/lib.rs`.
    The difference between the resulting number of lines and the number of lines measured before we have taken as the lines of annotation.
  + The size of the generated Coq code we measured by running `tokei case_studies/minivec/output/minivec/generated/generated_code_minivec.v`.
    Compared to the roughly 1500 lines of code given in the paper, the reported number in the artifact is lower due to changes to the code generation and the used Rust compiler version.
    We will update this metric in the final version of the paper.
  + The general theory for vectors is located in `case_studies/extra_proofs/minivec/minivec.v`.
    We measured the number of lines with `tokei case_studies/extra_proofs/minivec/minivec.v`.
  + The proof of `Vec::pop` is located in `case_studies/minivec/output/minivec/proofs/proof_Vec_T_pop.v`.
    When running the proof, the `rep` tactic will output the number of separation logic steps taken.
    You can confirm that the remaining five sideconditions are solved in about 20 lines of manual proofs.
  + The proof checking time for the vector case study has been measured with the Unix `time` command.
    We have measured the timing on a machine with an Apple M1 Max and 64GB RAM.
    Since submission time, the performance of RefinedRust has been slightly improved, so that the case study is checked in about 5 minutes and 40 seconds now.
    On different machines, the timing may be different.
    You can reproduce the times with the following commands:
    ```
    cd case_studies/minivec
    cargo clean && cargo refinedrust
    time dune build
    ```
