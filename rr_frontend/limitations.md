# Supported features

The RefinedRust frontend is currently restricted to a subset of Rust's features.
Over time, the feature support will grow.

## Soundly handled features
- Functions with loops, conditionals, matches, recursion
- Non-recursive structs and enums

## Features with limited support
- drop support is currently limited and drop code is not generated automatically. This will be lifted soon.
- Overflow-checking operations for +, -, and * are translated away since already Caesium's semantics has UB on overflows

## Unsupported features
- recursive types
- closures
- trait objects
- non-repr(rust) ADTs
- slices/fat pointers

## Known bugs
- Re-declared variables (e.g. `let x = 5; let x = (32, 43);`) are not handled properly
