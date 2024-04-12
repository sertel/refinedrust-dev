#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.spin")]
#![allow(unused)]

mod relax;
mod once;
mod rwlock;
