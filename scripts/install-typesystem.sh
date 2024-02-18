#!/bin/bash

# Installs RefinedRust in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

opam pin remove refinedrust -y
opam remove refinedrust -y
opam pin add refinedrust.dev $REFINEDRUST_ROOT -y
