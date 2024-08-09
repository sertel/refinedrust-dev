#![rr::include("ptr")]
#![rr::import("stdlib.alloc.theories", "layout")]
use std::ptr::Alignment;


#[rr::export_as(alloc::alloc::Layout)]
#[rr::refined_by("l" : "rust_layout")]
pub struct Layout {
    // size of the requested block of memory, measured in bytes.
    #[rr::field("l.(layout_sz)")]
    size: usize,

    // alignment of the requested block of memory, measured in bytes.
    // we ensure that this is always a power-of-two, because API's
    // like `posix_memalign` require it and it is a reasonable
    // constraint to impose on Layout constructors.
    //
    // (However, we do not analogously require `align >= sizeof(void*)`,
    //  even though that is *also* a requirement of `posix_memalign`.)
    #[rr::field("l.(layout_alignment)")]
    align: Alignment,
}

#[rr::export_as(alloc::alloc::Layout)]
impl Layout {
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("x.(layout_sz)")]
    pub const fn size(&self) -> usize {
        self.size
    }
}
