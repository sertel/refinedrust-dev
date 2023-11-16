#!/bin/bash
opam pin add coq-stdpp stdpp/
opam pin add coq-iris iris/
opam pin add coq-lambda-rust lambda-rust/

cd theories/
dune build
