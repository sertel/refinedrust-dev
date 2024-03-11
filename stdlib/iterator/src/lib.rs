#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::coq_prefix("stdlib.iterator")]

mod step;

#[rr::export_as(core::iter::traits::Iterator)]
pub trait Iterator {
    type Item;

    #[rr::params("a", "γ")]
    #[rr::args("(#a, γ)")]
    #[rr::exists("x")]
    #[rr::returns("x")]
    fn next(&mut self) -> Option<Self::Item>;


    // TODO: more methods
    // Basically, we should have a common interface for types implementing the Iterator trait, and
    // when we generate a specific instantiation, we want to instantiate that interface.
}
