
# Overview of attributes

Rust code can be annotated with attributes to provide specifications and other information to RefinedRust.
All RefinedRust attributes are prefixed with the name space `rr`.

## Function attributes
As an example, the following function has specifications attached to it that say that it adds `42` to an integer:

```rust
#[rr::params(z)]
#[rr::args("z")]
#[rr::requires("⌜z + 42 ∈ i32⌝")]
#[rr::returns("z + 42")]
fn add_42(x : i32) -> i32 {
  x + 42
}
```
The `params` clause specifies a universally-quantified parameter of the specification -- in this case, the (mathematical) integer `z` represented by the argument `x`.
The `args` clause specifies the refinement and (optionally) a type for the single argument `x` of the function. 
RefinedRust infers a "default" type for the argument from Rust's type, but this can also be overridden by providing an explicit type after a `@`.
For instance, the clause `#[rr::args("z" @ "int i32")]` would be equivalent to the one specified above.

The `requires` clause specifies the requirement that the result of the addition fits into an `i32`. This can in general include arbitrary Iris propositions.
Arbitrary Coq propositions (like `z+42 ∈ i32`) can be embedded into Iris by wrapping it with `⌜`/`⌝` brackets.
Finally, the returns clause specifies a refinement (and optionally, a type) for the return value of the function.


| Keyword   | Purpose                      | Properties | Example                          | 
--------------------------------------------------------------------------------------------------
| `params`  | specify Coq-level specification parameters | multiple   | `#[rr:params("n" : "Z", b : "bool")]` |
| `param`  | specify Coq-level parameters | multiple   | `#[rr:param("n" : "Z")]` |
| `args`    | specify argument refinements/types | multiple | `#[rr::args("n" @ "int i32", "b"]` |
| `returns` | specify return refinement/type | single | `#[rr::returns("42" @ "int i32")]` |
| `requires` | specify a precondition | multiple | `#[rr:requires("⌜i > 42⌝")]` | 
| `ensures` | specify a postcondition | multiple | `#[rr::ensures("⌜x > y⌝")]` |
| `exists`  | specify an existential for the postcondition | multiple | `#[rr::exists("x" : "Z")]` |


## Struct attributes
| Keyword   | Purpose                      | Properties | Example                          | 
--------------------------------------------------------------------------------------------------
| `refined_by` | Specify the refinement type of a struct | single | `#[rr::refined_by("(a, b, l)" : "(Z * Z * loc)")]` |
| `exists` | Specify an existentially abstracted mathematical value | multiple | `#[rr::exists("x" : "Z")]` |
| `invariant` | Specify an invariant on the struct type | multiple | `#[rr::invariant("#type "l" : "x" @ "int i32")]` |
| `refines` | Optionally specify the refinement of the raw struct type (can only be used when no refinements are specified via `field` attributes on the struct's fields) | single | `#[rr::refines("-[a; b]")]` |
| `mode`  | Specifies the sharing mode of the defined type: either `plain` (the default, invariants are shared on a best-effort basis for the sharing invariant) or `persistent` (all invariants need to be shareable) | `#[rr::mode("plain")]` |  

Invariants on structs can be prefixed by `#own` or `#shr` to only include the invariant in the struct's ownership or sharing predicate, respectively, e.g.: `#[rr::invariant(#own "freeable l len")]`. 

Struct fields can be annotated with a `field` attribute specifying the struct field's type and refinement in one of the following forms:
- `#[rr::field("l" @ "alias_ptr_t")]`, specifying a refinement and a type. No `refines` attribute should have been specified on the struct.
- `#[rr::field("l")]`, specifying just a refinement. No `refines` attribute should have been specified on the struct.
- `#[rr::field("alias_ptr_t")]`, specifying just a type. A `refines` attribute needs to have been specified on the struct.

## Enum attributes
Enums have a top-level `refined_by` attribute for specifying the enum's refinement type.
Each of the enum's variants is annotated with two attributes:
- a `pattern` attribute for matching on the enum's refinement type
- a `refinement` attribute for specifying the refinement of the variant's component type, often a tuple type.
  If a variant contains a nested struct, the struct can further be annotated with all the usual struct attributes.

For instance, the `option` type could be specified as follows, being refined by Coq's `option` type.
```rust
#[rr::refined_by("option (place_rfn {rt_of T})")]
enum option<T> {
    #[rr::pattern("None")]
    #[rr::refinement("-[]")] // can be left implicit
    None, 
    #[rr::pattern("Some(x)")]
    #[rr::refinement("-[x]")]
    Some(T),
}
```

## Special syntax
### Escape sequences
As a rule of thumb, all  string literals in specifications are inserted literally into the generated Coq code.
However, specifications can escape into special syntax inside `{ }` (curly braces) in order to access some Rust-level variables.
These escape sequences are literally replaced by the frontend.

In particular, we support the following escape sequences:
| Example | Purpose | 
-------------------------------------------------
| `{T}`   | Gets substituted by the RefinedRust type corresponding to the Rust type variable `T` |
| `{st_of T}` | Gets substituted by the syntactic type (providing layout information) of the type parameter `T` | 
| `{ly_of T}` | Gets substituted by a term giving the layout of the type parameter `T`'s syntactic type |
| `{rt_of T}` | Gets substituted by the refinement type (mathematical model) of the type parameter `T` |
| `{'a}` | Gets replaced by a term describing the lifetime of lifetime parameter 'a |

To prevent an expression wrapped in curly braces to be transformed, write two curly braces: `{{ ... }}`.
This will be replaced by `{ ... }`.

### Templates
RefinedRust offers notational shortcuts for some commonly-used specification patterns.

- Type assignments for locations/places can be specified by the `#type "l" : "r" @ "ty"` template, specifying that `l` is an owned pointer storing a value of type `r @ ty`.
  This is allowed in `requires` and `ensures` clauses on functions, as well as in `invariant` clauses on struct definitions.

## Types
TODO: provide an overview of RefinedRust types.
