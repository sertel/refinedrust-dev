#!/bin/bash

# Installs RefinedRust in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

opam pin add coq-lithium.dev $REFINEDRUST_ROOT -y
opam pin add refinedrust.dev $REFINEDRUST_ROOT -y
