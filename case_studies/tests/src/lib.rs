#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(stmt_expr_attributes)]
#![allow(dead_code)]

mod char;
mod enums;
mod inline;
mod structs;
mod traits;
mod statics;

mod vec_client;
mod mixed;
mod closures;
mod references;
mod option;
mod consts;
