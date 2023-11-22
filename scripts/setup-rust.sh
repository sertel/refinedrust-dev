#!/bin/bash

# Installs rustup and builds the frontend.
# Inputs: 
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

cd $REFINEDRUST_ROOT
cargo install rustup-toolchain-install-master
./rr_frontend/rustup-toolchain
./rr_frontend/refinedrust build
