#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![feature(allocator_api)]
#![rr::coq_prefix("stdlib.alloc")]

use std::ptr::NonNull;
use std::alloc::{Allocator, AllocError, Layout};

#[rr::export_as(alloc::alloc::Global)]
pub struct Global {

}

unsafe impl Allocator for Global {
    fn allocate(&self, layout: Layout) -> Result<NonNull<[u8]>, AllocError> {
        unimplemented!();
    }

    unsafe fn deallocate(&self, ptr: NonNull<u8>, layout: Layout) {
        unimplemented!();
    }
}


