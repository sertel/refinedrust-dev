#!/bin/bash

# Installs RefinedRust stdlib in the current opam switch.
# Inputs:
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

opam pin remove refinedrust-stdlib -y
opam remove refinedrust-stdlib -y
opam pin add refinedrust-stdlib.dev $REFINEDRUST_ROOT/stdlib -y
