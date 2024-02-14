// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use polonius_engine::FactTypes;
use rustc_borrowck::consumers::RustcFacts;
use rustc_middle::mir::Location;

pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

/// Error type used for the MIR to Caesium translation.
//TODO: add location info based on Span
#[derive(Debug, Clone)]
pub enum TranslationError {
    UnsupportedFeature { description: String },
    UnsupportedType { description: String },
    Unimplemented { description: String },
    InvalidLayout,
    UnknownVar(String),
    UnknownError(String),
    FatalError(String),
    LoanNotFound(Location),
    AttributeError(String),
    UnknownAttributeParser(String),
    UnknownProcedure(String),
}
