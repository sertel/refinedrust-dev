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
#[rr::context("FnOnce {rt_of Self} {rts_of Args} {rt_of Output}")]
pub trait FnOnce2<Args: Tuple> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::params("m", "x")]
    #[rr::args("m", "x")]
    #[rr::exists("y")]
    #[rr::ensures("fnonce_call_rel m x y")]
    #[rr::returns("y")]
    fn call_once(self, args: Args) -> Self::Output;
}


#[rr::export_as(core::ops::FnOnce)]
#[rr::parameter("H: FnOnce2")]
pub trait FnOnce3<Args: Tuple> {
    /// The returned type after the call operator is used.
    type Output;

    /// Performs the call operation.
    #[rr::spec("H.(fnonce_call_spec)")] 
    fn call_once(self, args: Args) -> Self::Output;
}


*/
