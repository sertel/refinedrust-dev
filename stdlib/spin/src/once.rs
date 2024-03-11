#![rr::import("stdlib.spin.theories.once", "once_ghost_state")]
#![rr::include("option")]

use crate::relax::*;

// Point: how can we make this somewhat ergonomic? 
// We should ideally automatically include this in the context (of a function) when we instantiate
// this ADT.
//
// We could factor this into a definition that takes the refinement types as argument. 
// Then we could also include this in the interface definition

#[rr::refined_by("η" : "gname")]
#[rr::context("onceG Σ ({rt_of T})")]
#[rr::export_as(spin::once::Once)]
#[rr::exists("x", "y")]
//#[rr::exists("o" : "option {rt_of T}")]
//#[rr::invariant(#own "once_status_tok η o")]
pub struct Once<T = (), R = Spin> {
    #[rr::field("x")]
    _r: R,
    #[rr::field("y")]
    _d: T,
}

#[rr::only_spec]
#[rr::export_as(spin::once::Once)]
#[rr::context("onceG Σ ({rt_of T})")]
impl<T, R: RelaxStrategy> Once<T, R> {
    #[rr::skip]
    #[rr::params("η", "f")]
    #[rr::args("#η", "f")]
    #[rr::requires("once_status_tok η None")]
    // TODO: specify that the closure has a particular spec
    #[rr::exists("x")]
    #[rr::ensures("once_status_tok η (Some x)")]
    #[rr::returns("#x")]
    pub fn call_once<F: FnOnce() -> T>(&self, f: F) -> &T {
        unimplemented!();
    }
}

#[rr::only_spec]
#[rr::export_as(spin::once::Once)]
#[rr::context("onceG Σ ({rt_of T})")]
impl<T, R> Once<T, R> {
    /// Creates a new [`Once`].
    #[rr::exists("η")]
    #[rr::ensures(#iris "once_status_tok η None")]
    #[rr::returns("η")]
    pub const fn new() -> Self {
        unimplemented!();
    }

    /// Creates a new initialized [`Once`].
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::exists("η")]
    #[rr::ensures(#iris "once_status_tok η (Some x)")]
    #[rr::returns("η")]
    pub const fn initialized(data: T) -> Self {
        unimplemented!();
    }

    /// Returns a reference to the inner value if the [`Once`] has been initialized.
    #[rr::params("η", "o")]
    #[rr::args("#η")]
    #[rr::requires(#iris "once_status_tok η o")]
    #[rr::ensures(#iris "once_status_tok η o")]
    #[rr::returns("<#>@{option}<#>@{option} o")]
    pub fn get(&self) -> Option<&T> {
        unimplemented!();
    }

    #[rr::params("η", "o")]
    #[rr::args("#η")]
    #[rr::requires(#iris "once_status_tok η o")]
    #[rr::ensures(#iris "once_status_tok η o")]
    #[rr::returns("bool_decide (is_Some o)")]
    pub fn is_completed(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("γ", "η", "o")]
    #[rr::args("(#η, γ)")]
    #[rr::requires(#iris "once_status_tok η o")]
    #[rr::exists("o'" : "option (place_rfn {rt_of T} * gname)%type")]
    #[rr::observe("γ": "η")]
    #[rr::returns("<#>@{option} o'")]
    #[rr::ensures(#iris "if bool_decide (is_Some o)
                    then
                        ∃ (x : {rt_of T}) γ2, 
                            ⌜o' = Some (#x, γ2)⌝ ∗ ⌜o = Some x⌝ ∗
                            Inherit {'a} InheritGhost (∃ x', gvar_obs γ2 x' ∗ once_status_tok η (Some x'))
                    else ⌜o' = None⌝ ∗ once_status_tok η o")]
    pub fn get_mut<'a>(&'a mut self) -> Option<&'a mut T> {
        unimplemented!();
    }
}
