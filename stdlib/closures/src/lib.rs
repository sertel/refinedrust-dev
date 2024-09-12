#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::import("stdlib.closures.theories", "closures")]
#![rr::coq_prefix("stdlib.closures")]

#[rr::export_as(core::marker::Tuple)]
pub trait Tuple { }

/*
#[rr::export_as(core::ops::Fn)]
pub trait Fn<Args: Tuple>: FnMut<Args> {

    /// Performs the call operation.
    fn call(&self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::FnMut)]
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    /// Performs the call operation.
    fn call_mut(&mut self, args: Args) -> Self::Output;
}
*/

#[rr::export_as(core::ops::FnOnce)]
pub trait FnOnce<Args: Tuple> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::params("m", "x")]
    #[rr::args("m", "x")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn call_once(self, args: Args) -> Self::Output;
}

/*
#[rr::export_as(core::ops::FnOnce)]
#[rr::exists("Pre" : "{rt_of Self} → {rt_of Args} → iProp Σ")]
#[rr::exists("Post" : "{rt_of Self} → {rt_of Args} → {rt_of Output} → iProp Σ")]
pub trait FnOnce<Args: Tuple> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::params("m", "x")]
    #[rr::requires("Pre m x")]
    #[rr::args("m", "x")]
    #[rr::exists("y")]
    #[rr::ensures("Post m x y")]
    #[rr::returns("y")]
    fn call_once(self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::FnMut)]
#[rr::exists("Pre" : "{rt_of Self} → {rt_of Args} → iProp Σ")]
// Note: the relation gets both the current and the next state
#[rr::exists("Post" : "{rt_of Self} → {rt_of Args} → {rt_of Self} → {rt_of Output} → iProp Σ")]
pub trait FnMut<Args: Tuple>: FnOnce<Args> {
    /// Performs the call operation.
    #[rr::params("m", "γ", "x")]
    #[rr::requires("Pre m x")]
    #[rr::args("(#m, γ)", "x")]
    #[rr::exists("y", "m'")]
    #[rr::ensures("Post m x m' y")]
    #[rr::observe("γ": "m'")]
    #[rr::returns("y")]
    fn call_mut(&mut self, args: Args) -> Self::Output;
}

#[rr::export_as(core::ops::Fn)]
#[rr::exists("Pre" : "{rt_of Self} → {rt_of Args} → iProp Σ")]
#[rr::exists("Post" : "{rt_of Self} → {rt_of Args} → {rt_of Output} → iProp Σ")]
pub trait Fn<Args: Tuple>: FnMut<Args> {

    /// Performs the call operation.
    #[rr::params("m", "x")]
    #[rr::requires("Pre m x")]
    #[rr::args("#m", "x")]
    #[rr::exists("y")]
    #[rr::ensures("Post m x y")]
    #[rr::returns("y")]
    fn call(&self, args: Args) -> Self::Output;
}
*/
