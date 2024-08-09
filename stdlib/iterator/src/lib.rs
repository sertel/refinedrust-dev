#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::coq_prefix("stdlib.iterator")]
#![rr::include("closures")]

mod step;
pub mod adapters;
pub mod traits;

