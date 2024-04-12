#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.alloc")]
#![allow(unused)]

use std::ptr::NonNull;
use std::alloc::{Allocator, AllocError, Layout};

#[rr::export_as(alloc::alloc::Global)]
pub struct Global {

}

impl Global {
    #[rr::only_spec]
    fn foo(&self) {

    }
}

unsafe impl Allocator for Global {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unimplemented!();
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unimplemented!();
    }
}


