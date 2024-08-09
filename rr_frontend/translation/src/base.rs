// © 2023, The RefinedRust Developers and Contributors
//
// This Source Code Form is subject to the terms of the BSD-3-clause License.
// If a copy of the BSD-3-clause license was not distributed with this
// file, You can obtain one at https://opensource.org/license/bsd-3-clause/.

use derive_more::Display;
use rr_rustc_interface::borrowck::consumers::RustcFacts;
use rr_rustc_interface::middle::mir::Location;
use rr_rustc_interface::polonius_engine::FactTypes;

use crate::trait_registry::Error;

pub type Region = <RustcFacts as FactTypes>::Origin;
pub type Loan = <RustcFacts as FactTypes>::Loan;
pub type PointIndex = <RustcFacts as FactTypes>::Point;
pub type Variable = <RustcFacts as FactTypes>::Variable;
pub type Path = <RustcFacts as FactTypes>::Path;

/// Error type used for the MIR to Caesium translation.
//TODO: add location info based on Span
#[derive(Clone, Debug, Display)]
pub enum TranslationError<'tcx> {
    #[display("Unsupported Feature: {}", description)]
    UnsupportedFeature { description: String },
    #[display("Unsupported Type: {}", description)]
    UnsupportedType { description: String },
    #[display("Unimplemented Case: {}", description)]
    Unimplemented { description: String },
    #[display("Invalid Layout")]
    InvalidLayout,
    #[display("Unknown Variable: {}", _0)]
    UnknownVar(String),
    #[display("Unknown Error: {}", _0)]
    UnknownError(String),
    #[display("Fatal Error: {}", _0)]
    FatalError(String),
    #[display("Loan was not found at location {:?}", _0)]
    LoanNotFound(Location),
    #[display("Attribute is ill-formed: {}", _0)]
    AttributeError(String),
    #[display("Configured attribute-parser is unknown: {}", _0)]
    UnknownAttributeParser(String),
    #[display("Unknown procedure: {}", _0)]
    UnknownProcedure(String),
    #[display("Trait could not be resolved: {}", _0)]
    TraitResolution(String),
    #[display("Trait translation failed: {}", _0)]
    TraitTranslation(Error<'tcx>),
    #[display("Procedure could not be registered: {}", _0)]
    ProcedureRegistry(String),
}

impl<'tcx> From<Error<'tcx>> for TranslationError<'tcx> {
    fn from(x: Error<'tcx>) -> Self {
        Self::TraitTranslation(x)
    }
}
