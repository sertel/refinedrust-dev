#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.ptr")]
#![allow(unused)]

mod alignment;

/*
#[rr::export_as(core::ptr::invalid_mut)]
#[rr::shim("ptr_dangling", "type_of_ptr_dangling")]
pub const fn invalid_mut<T>(addr: usize) -> *mut T {
    unimplemented!();
}
*/
