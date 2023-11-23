#!/bin/bash

# Installs RefinedRust in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

opam install coq-lithium.dev $REFINEDRUST_ROOT -y
opam install refinedrust.dev $REFINEDRUST_ROOT -y
