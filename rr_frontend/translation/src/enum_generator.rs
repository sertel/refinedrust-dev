// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use log::info;

use rustc_hir::def_id::DefId;
use rustc_middle::ty as ty;
use rustc_middle::ty::{Ty, IntTy, UintTy, TyKind};
//use rustc_middle::mir::Field;
use crate::rustc_middle::ty::TypeFoldable;

use std::cell::RefCell;
use std::collections::{HashMap, HashSet};
use std::ops::DerefMut;
use std::fmt::Write;

use typed_arena::Arena;

use crate::environment::Environment;

use radium;

use crate::spec_parsers::struct_spec_parser::{self, InvariantSpecParser, StructFieldSpecParser};
use crate::spec_parsers::enum_spec_parser::{VerboseEnumSpecParser, EnumSpecParser};

use crate::tyvars::*;
pub use crate::base::*;

struct CoqParamList(Vec<(radium::CoqName, radium::CoqType)>);

impl CoqParamList {

}

struct CoqVariant {
    name: String,
    params: CoqParamList,
}

struct CoqInductive {
    parameters: CoqParamList,
    variants: Vec<CoqVariant>,
}

enum CoqTopLevelAssertion {
    InductiveDecl(CoqInductive),
}

/// Given a Rust enum which has already been registered and whose fields have been translated, generate a corresponding Coq Inductive as well as an EnumSpec.
fn generate_enum_spec<'tcx>(def: ty::AdtDef<'tcx>) -> (CoqInductive, radium::EnumSpec) {
    unreachable!();

    // TODO:
    // The algorithm: just go over the variants.
    // For each variant, query the already translated type that we generated.
    // - find out how many arguments, aka fields. 
    //      Generate names for those, as well as find out the CoqType of the refinement.
    // - generate a variant with these arguments 
    // - the generated spec should essentially take those
}


