#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![feature(ptr_alignment_type)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.alloc")]
#![allow(unused)]

mod layout;
use layout::*;

use std::ptr::NonNull;
use std::alloc::{AllocError};

#[rr::export_as(alloc::alloc::Global)]
pub struct Global {

}

impl Global {
    #[rr::skip]
    fn foo(&self) {

    }
}

unsafe impl Allocator for Global {
    //fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        //unimplemented!();
    //}

    //unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        //unimplemented!();
    //}
}

#[rr::export_as(alloc::alloc::Allocator)]
pub unsafe trait Allocator {
    // Required methods
    //fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError>;
    //unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout);
}
