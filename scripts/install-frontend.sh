#!/bin/bash

# Installs the frontend.
# Inputs: 
# - REFINEDRUST_ROOT: the root directory of the RefinedRust checkout

cd $REFINEDRUST_ROOT/rr_frontend && ./refinedrust install
