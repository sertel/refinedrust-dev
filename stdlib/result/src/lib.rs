#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.result")]
#![allow(unused)]

#![rr::import("stdlib.result.theories", "result")]

use std::fmt;

#[rr::export_as(core::result::Result)]
#[rr::refined_by("result (place_rfn {rt_of T}) (place_rfn {rt_of E})")]
pub enum Result<T, E> {
    #[rr::export_as(core::result::Result::Ok)]
    #[rr::pattern("Ok" $ "x")]
    #[rr::refinement("-[x]")]
    Ok(T),
    #[rr::export_as(core::result::Result::Err)]
    #[rr::pattern("Err" $ "x")]
    #[rr::refinement("-[x]")]
    Err(E),
}

#[rr::export_as(core::result::Result)]
#[rr::only_spec]
impl<T, E> Result<T, E> {

    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("bool_decide (is_Ok x)")]
    pub fn is_ok(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("bool_decide (is_Err x)")]
    pub fn is_err(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("Ok (#x)")]
    #[rr::returns("x")]
    pub fn unwrap(self) -> T where E: fmt::Debug {
        unimplemented!();
    }
}
