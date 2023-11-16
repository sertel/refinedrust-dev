#!/bin/bash

opam switch create . --packages=ocaml-variants.4.14.0+options,ocaml-option-flambda --no-install
eval $(opam env)
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add coq 8.17.1
opam pin add coq-stdpp stdpp/
opam pin add coq-stdpp-unstable stdpp/
opam pin add coq-iris iris/
opam pin add coq-lambda-rust.dev lambda-rust/
make builddep

cd theories/
dune build
