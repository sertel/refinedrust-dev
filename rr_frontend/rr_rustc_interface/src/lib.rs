// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

//! Wrapper around rustc interfaces, preparing for smir.
#![feature(rustc_private)]

pub extern crate polonius_engine as polonius_engine;
pub extern crate rustc_abi as abi;
pub extern crate rustc_ast as ast;
pub extern crate rustc_attr as attr;
pub extern crate rustc_data_structures as data_structures;
pub extern crate rustc_driver as driver;
pub extern crate rustc_errors as errors;
//pub extern crate rustc_errors as errors;
//pub extern crate rustc_index as index;
pub extern crate rustc_infer as infer;
pub extern crate rustc_interface as interface;
pub extern crate rustc_session as session;
pub extern crate rustc_span as span;
pub extern crate rustc_target as target;

// TODO use smir instead
pub extern crate rustc_borrowck as borrowck;
pub extern crate rustc_hir as hir;
pub extern crate rustc_middle as middle;
pub extern crate rustc_mir_dataflow as dataflow;
pub extern crate rustc_trait_selection as trait_selection;

//pub extern crate rustc_smir;
//pub use rustc_smir::very_unstable::{borrowck, dataflow, hir, middle, trait_selection};
