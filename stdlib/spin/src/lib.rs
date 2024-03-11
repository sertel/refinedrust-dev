#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::coq_prefix("stdlib.spin")]

mod relax;
mod once;
