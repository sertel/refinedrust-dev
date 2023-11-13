#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![feature(let_else)]
//#![rr::header("From refinedrust.examples Require Import alloc_shims.")]

/// Vec implementation from https://doc.rust-lang.org/nomicon/vec/vec-final.html

use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};
use std::ptr::{self, NonNull};

fn main() {

}


#[rr::returns("()")]
fn get_mut_client() {

    //let mut x = vec![100, 200, 300];
    let mut x = Vec::new();
    x.push(100);
    x.push(200);
    x.push(300);

    let xr = x.get_mut(1).unwrap();
    assert!(*xr == 200);
    *xr = 42;
    assert!(*x.get_mut(1).unwrap() == 42);
}



/// This creates a wrapper around the Rust Alloc API that always fails on allocation failures.
/// The methods will be fully replaced by shims that implement the same functionality in terms of
/// the primitives of our language model.
/// TODO: we may gradually refine these abstractions to get closer to the actual Rust APIs.
///
/// General assumptions we make:
/// - the global allocator has _not_ been reconfigured to not abort on allocation failure,
///   in particular we assume that the allocation failure handler does not panic.
mod RRAlloc {
    use std::alloc::{self, Layout};

    #[rr::shim("alloc_array", "type_of_alloc_array")]
    pub unsafe fn alloc_array<T>(len: usize) -> *mut T {
        assert!(len > 0);
        // checks that size is ≤ MaxInt isize
        let ly = Layout::array::<T>(len).unwrap();

        // will return null on alloc failure due to
        // - memory exhaustion (but abortion is also allowed behavior in this case)
        // - `ly` not meeting the allocator's size or alignment constraints
        let ptr = alloc::alloc(ly);
        if ptr.is_null() {
            // due to our assumption, this will abort.
            alloc::handle_alloc_error(ly);
        }
        ptr as *mut T
    }

    // For preconditions, see the preconditions of the shim.
    #[rr::shim("realloc_array", "type_of_realloc_array")]
    pub unsafe fn realloc_array<T>(old_len: usize, ptr: *mut T, new_len: usize) -> *mut T {
        assert!(new_len > 0);
        // fine: checks that size is ≤ MaxInt isize
        let old_layout = Layout::array::<T>(old_len).unwrap();
        // fine: same reason
        let new_layout = Layout::array::<T>(new_len).unwrap();

        // will return null on realloc failure -- in this case, the original ptr stays intact
        //    => We directly abort here to match the semantics of our shim
        // - new_len is rounded up to nearest multiple of alignment, and this value must be < usize_max (yes, strictly!)
        //   => trivially satisfied since we have an array layout
        // - the layout with which it was allocated is the same as old_layout
        //   => ensured by the freeable precondition
        // - we rely here on the fact that old_layout and new_layout will have the same alignment
        //   => trivial due to how we construct the layouts
        // - internally, these functions rely on the fact that rustc guarantees that type alignment is a power of 2
        //   => we also have that guarantee by design
        // - the array layout seems to rely on the fact that size is divisible by alignment, as it
        //   does not account for any padding to handle alignment
        //   => we also handle it that way for now

        let ptr = alloc::realloc(ptr as *mut u8, old_layout, new_layout.size());
        if ptr.is_null() {
            // due to our assumption, this will abort.
            alloc::handle_alloc_error(new_layout);
        }
        ptr as *mut T
    }

    #[rr::shim("free_array", "type_of_free_array")]
    pub unsafe fn dealloc_array<T>(len: usize, ptr: *mut T) {
        alloc::dealloc(ptr as *mut u8, Layout::array::<T>(len).unwrap());
    }

    /// Check that an array of `T` with length `len` is layoutable.
    #[rr::shim("check_array_layoutable", "type_of_check_array_layoutable")]
    pub fn check_array_layoutable<T>(len: usize) -> bool {
        let layout = Layout::array::<T>(len);
        layout.is_ok()
    }
}

/// A wrapper module around ptr operations we need.
/// TODO: gradually refine the shims here. We could for instance also just have a shim
/// for the `copy_nonoverlapping` intrinsic and properly implement the rest on top.
mod RRPtr {
    use std::ptr;
    use std::ptr::NonNull;

    #[rr::shim("ptr_write", "type_of_ptr_write")]
    pub unsafe fn write<T>(dst: *mut T, src: T) {
        // shim just does a typed write in Caesium
        ptr::write(dst, src)
    }

    #[rr::shim("ptr_read", "type_of_ptr_read")]
    pub unsafe fn read<T>(src: *const T) -> T {
        // shim just does a typed read in Caesium
        ptr::read(src)
    }

    #[rr::shim("ptr_copy", "type_of_ptr_copy")]
    pub unsafe fn copy<T>(src: *const T, dst: *mut T, count: usize) {
        // the shim will implement this via a loop with untyped reads/writes
        ptr::copy(src, dst, count)
    }

    #[rr::shim("ptr_dangling", "type_of_ptr_dangling")]
    pub fn dangling<T>() -> *mut T{
        NonNull::dangling().as_ptr()
    }

    // TODO: we currently only need these shims because we cannot register shims for std::mut_ptr::add etc. properly in the frontend.
    // Need to figure out how to get their DefIds properly.
    #[rr::shim("ptr_offset", "type_of_ptr_offset")]
    pub unsafe fn mut_offset<T>(ptr: *mut T, count: isize) -> *mut T {
        ptr.offset(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_offset")]
    pub unsafe fn const_offset<T>(ptr: *const T, count: isize) -> *const T {
        ptr.offset(count)
    }
    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn mut_add<T>(ptr: *mut T, count: usize) -> *mut T {
        ptr.add(count)
    }

    #[rr::shim("ptr_add", "type_of_ptr_add")]
    pub unsafe fn const_add<T>(ptr: *const T, count: usize) -> *const T {
        ptr.add(count)
    }
}



























































/// Represents an owned chunk of memory of which a prefix `xs` is filled with elements of type `T`,
/// with a total capacity to hold `cap` elements of `T`.
// Compared to the Rustonomicon implementation, we use *const T instead of NonNull<T>.
// The only difference is that the null bitpattern can't be used for niche optimizations in our case.
#[rr::refined_by("(l, cap)" : "(loc * nat)")]
// only part of the invariant for the ownership predicate, not sharing
#[rr::invariant(#own "freeable_nz l (size_of_array_in_bytes {st_of T} cap) 1 HeapAlloc")]
pub struct RawVec<T> {
    // *const T because it is covariant in T
    #[rr::field("l")]
    ptr: *const T,
    #[rr::field("Z.of_nat cap")]
    cap: usize,
    #[rr::field("tt")]
    _marker: PhantomData<T>,
}

#[rr::refined_by("xs" : "list (place_rfn {rt_of T})")]
#[rr::exists("cap" : "nat", "l" : "loc", "len" : "nat", "els")]
#[rr::invariant(#type "l" : "els" @ "array_t (maybe_uninit {T}) cap")]
#[rr::invariant("⌜xs = project_vec_els len els⌝")]
#[rr::invariant("⌜∀ i, (0 ≤ i < len)%nat → els !! i = Some (#(Some (xs !!! i)))⌝")]
#[rr::invariant("⌜∀ i, (len ≤ i < cap)%nat → els !! i = Some (#None)⌝")]
#[rr::invariant("⌜len = length xs⌝")]
#[rr::invariant("⌜len ≤ cap⌝")]
// invariant due to GEP / ptr::offset limits: the total size of the allocation should not exceed isize::max bytes
// we need the ZST case to know that we never call grow except when we have reached the capacity limit
// TODO would be nice if we could deduplicate that with RawVec.
#[rr::invariant("⌜if decide (size_of_st {st_of T} = 0%nat) then cap = Z.to_nat (MaxInt usize_t) else (size_of_array_in_bytes {st_of T} cap ≤ MaxInt isize_t)%Z⌝")]
pub struct Vec<T> {
    #[rr::field("(l, cap)")]
    buf: RawVec<T>,
    #[rr::field("Z.of_nat $ len")]
    len: usize,
}

impl<T> RawVec<T> {
    // needed for VecDeque
    #[rr::params("l", "cap")]
    #[rr::args("#(l, cap)")]
    #[rr::returns("l" @ "alias_ptr_t")]
    pub fn ptr(&self) -> *mut T {
        self.ptr as *mut T
    }

    // needed for VecDeque
    #[rr::params("l", "cap")]
    #[rr::args("#(l, cap)")]
    #[rr::returns("cap")]
    pub fn cap(&self) -> usize {
        self.cap
    }

    // needed for VecDeque
    pub fn with_capacity(capacity: usize) -> Self {
        if mem::size_of::<T>() == 0 || capacity == 0 {
            Self {
                ptr: RRPtr::dangling(),
                cap: capacity,
                _marker: PhantomData,
            }
        }
        else {
            assert!(
                RRAlloc::check_array_layoutable::<T>(capacity),
                "Allocation too large"
            );

            let ptr = unsafe { RRAlloc::alloc_array::<T>(capacity) };

            Self {
                ptr: ptr as *const T,
                cap: capacity,
                _marker: PhantomData,
            }
        }
    }

    #[rr::exists("l" : "loc", "cap" : "nat")]
    #[rr::ensures("⌜cap = if decide (size_of_st {st_of T} = 0%nat) then Z.to_nat (MaxInt usize_t) else 0%nat⌝")]
    #[rr::ensures(#type "l" : "(replicate cap #None)" @ "array_t (maybe_uninit {T}) cap")]
    #[rr::returns("(l, cap)")]
    #[rr::tactics("all: rewrite /size_of_array_in_bytes; simplify_layout_goal; lia.")]
    pub fn new() -> Self {
        // !0 is usize::MAX. This branch should be stripped at compile time.
        let cap = if mem::size_of::<T>() == 0 { !0 } else { 0 };

        // `NonNull::dangling()` doubles as "unallocated" and "zero-sized allocation"
        RawVec {
            ptr: RRPtr::dangling(),
            cap: cap,
            _marker: PhantomData,
        }
    }

    #[rr::params("l", "xs", "cap" : "nat", "γ")]
    #[rr::args("(#(l, cap), γ)")]
    #[rr::requires("⌜(size_of_array_in_bytes {st_of T} (2 * cap) ≤ MaxInt isize_t)%Z⌝")]
    #[rr::requires("⌜(size_of_st {st_of T} > 0)%Z⌝")]
    #[rr::requires(#type "l" : "xs" @ "array_t (maybe_uninit {T}) cap")]
    #[rr::exists("new_cap" : "nat", "l'" : "loc")]
    #[rr::ensures("gvar_pobs γ (l', new_cap)")]
    #[rr::ensures(#type "l'" : "(xs ++ replicate (new_cap - cap) #None)" @ "array_t (maybe_uninit {T}) new_cap")]
    #[rr::ensures("⌜new_cap > cap⌝")]
    #[rr::ensures("⌜(size_of_array_in_bytes {st_of T} new_cap ≤ MaxInt isize_t)%Z⌝")]
    pub fn grow(&mut self) {
        // unfold invariant - it will be broken quite consistently throughout
        // also need to learn the pure facts to pass all the checks.

        // since we set the capacity to usize::MAX when T has size 0,
        // getting to here necessarily means the Vec is overfull.
        assert!(mem::size_of::<T>() != 0, "capacity overflow");
        // from here on: can assume we don't have a ZST

        let new_cap = if self.cap == 0 {
            // in this case, layouting of the array should never fail
            // we need the fact that size_of T ≤ isize::MAX for that.
            1
        } else {
            // This can't overflow because we ensure self.cap <= isize::MAX,
            // unless the type is a ZST
            let new_cap = 2 * self.cap;
            new_cap
        };

        // Ensure that the new allocation doesn't exceed `isize::MAX` bytes.
        // This limit is due to GEP / ptr::offset taking isize offsets, so Rust std generally
        // limits allocations to isize::MAX bytes.
        assert!(
            RRAlloc::check_array_layoutable::<T>(new_cap),
            "Allocation too large"
        );

        let new_ptr = if self.cap == 0 {
            unsafe { RRAlloc::alloc_array::<T>(new_cap) }
        } else {
            // this works because we have already checked that the new array is layoutable
            let old_ptr = self.ptr;
            unsafe { RRAlloc::realloc_array::<T>(self.cap, old_ptr as *mut T, new_cap) }
        };

        // move ownership into self.ptr
        self.ptr = new_ptr as *const T;
        self.cap = new_cap;

        // fold invariant
    }
}

impl<T> Vec<T> {

    // private function, take an unfolded type
    // we do not move ownership out, but return an alias to the ptr
    #[rr::params("l" : "loc", "cap" : "nat", "len" : "Z")]
    // TODO: clarify the semantics of the raw part.
    //#[rr::args(#raw "#-[#(l, cap); #len]")]
    #[rr::args(#raw "#(-[#(l, cap); #len])" @ "shr_ref (Vec_ty {T}) {'a}")]
    #[rr::returns("l" @ "alias_ptr_t")]
    fn ptr<'a>(&'a self) -> *mut T {
        self.buf.ptr() as *mut T
    }

    // private function, take an unfolded type
    #[rr::params("l" : "loc", "cap" : "nat", "len" : "Z")]
    // TODO: clarify the semantics of the raw part.
    //#[rr::args(#raw "#(-[#(l, cap); #len])")]
    #[rr::args(#raw "#(-[#(l, cap); #len])" @ "shr_ref (Vec_ty {T}) {'a}")]
    #[rr::returns("cap")]
    fn cap<'a>(&'a self) -> usize {
        self.buf.cap
    }

    #[rr::params("xs")]
    #[rr::args("#xs")]
    #[rr::returns("length xs")]
    pub fn len(&self) -> usize {
        self.len
    }

    #[rr::returns("[]")]
    pub fn new() -> Self {
        Vec {
            buf: RawVec::new(),
            len: 0,
        }
    }

    #[rr::params("xs", "γ", "x")]
    #[rr::args("(#xs, γ)", "x")]
    #[rr::requires("⌜(length xs < MaxInt usize_t)%Z⌝")]
    #[rr::requires("⌜(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ MaxInt isize_t)%Z⌝")]
    #[rr::ensures("gvar_pobs γ (xs ++ [ #x])")]
    pub fn push(&mut self, elem: T) {
        if self.len == self.cap() {
            self.buf.grow();
        }

        // important: ptr::write does not call drop on the uninit mem.
        unsafe {
            ptr::write(RRPtr::mut_add(self.ptr(), self.len), elem);
        }

        // Can't overflow, we'll OOM first.
        self.len += 1;
    }

    #[rr::params("xs", "γ")]
    #[rr::args("(#(fmap (M:=list) PlaceIn xs), γ)")]
    #[rr::returns("fmap PlaceIn (last xs)")]
    #[rr::ensures("gvar_pobs γ (take (length xs - 1) (fmap (M:=list) PlaceIn xs))")]
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            None
        } else {
            self.len -= 1;
            unsafe { Some(ptr::read(RRPtr::mut_add(self.ptr(), self.len))) }
        }
    }

    #[rr::params("xs", "γ", "i" : "nat", "x")]
    #[rr::args("(#xs, γ)", "Z.of_nat i", "x")]
    #[rr::requires("⌜i ≤ length xs⌝")]
    #[rr::requires("⌜(length xs < MaxInt usize_t)%Z⌝")]
    #[rr::requires("⌜(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ MaxInt isize_t)%Z⌝")]
    // TODO: This spec is wrong. It should move the values in xs to the right
    #[rr::ensures("gvar_pobs γ (<[i := #x]> xs)")]
    pub fn insert(&mut self, index: usize, elem: T) {
        assert!(index <= self.len, "index out of bounds");
        if self.cap() == self.len {
            self.buf.grow();
        }

        unsafe {
            // doing a memmove, effectively
            // we will want to spec this in terms of our array type
            ptr::copy(
                RRPtr::mut_add(self.ptr(), index),
                RRPtr::mut_add(self.ptr(), index + 1),
                self.len - index,
            );
            ptr::write(RRPtr::mut_add(self.ptr(), index), elem);
            self.len += 1;
        }
    }

    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(#(fmap (M:=list) PlaceIn xs), γ)", "Z.of_nat i")]
    #[rr::requires("⌜i < length xs⌝")]
    #[rr::ensures("gvar_pobs γ (delete i (fmap (M:=list) PlaceIn xs))")]
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        unsafe {
            self.len -= 1;
            let result = ptr::read(RRPtr::mut_add(self.ptr(), index));
            // memmove
            ptr::copy(
                RRPtr::mut_add(self.ptr(), index + 1),
                RRPtr::mut_add(self.ptr(), index),
                self.len - index,
            );
            result
        }
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(fmap (M:=list) PlaceIn xs), γ)", "Z.of_nat i")]
    #[rr::requires("⌜i < length xs⌝")]
    #[rr::exists("γi")]
    #[rr::returns("(#(xs !!! i), γi)")]
    #[rr::ensures("gvar_pobs γ (<[i := PlaceGhost γi]> (fmap (M:=list) PlaceIn xs))")]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        // TODO this is needed to force invariant unfolding before the shared borrow for self.ptr.
        self.len;
        unsafe {
            let p = RRPtr::mut_add(self.ptr(), index);
            let ret = &mut *p;
            ret
        }
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(fmap (M:=list) PlaceIn xs), γ)", "Z.of_nat i")]
    // NOTE: currently , we need a sligtly more complicated specification that explicitly closes under ghost variable equivalence
    #[rr::exists("γi", "γ1", "γ2")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i), γi)) else None")]
    #[rr::ensures("if decide (i < length xs) then Inherit {'a} InheritGhost (Rel2 γ2 γ (eq (A:=list (place_rfn T_rt)))) else True")]
    #[rr::ensures("gvar_pobs γ2 (if decide (i < length xs) then <[i := PlaceGhost γ1]> (fmap (M:=list) PlaceIn xs) else fmap (M:=list) PlaceIn xs)")]
    #[rr::ensures("if decide (i < length xs) then Inherit {'a} InheritGhost (Rel2 γi γ1 (eq (A:=T_rt))) else True")]
    pub fn get_mut<'a>(&'a mut self, index: usize) -> Option<&'a mut T> {
        if (index < self.len()) {
            unsafe { Some (self.get_unchecked_mut(index)) }
        }
        else {
            None
        }
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(fmap (M:=list) PlaceIn xs)", "Z.of_nat i")]
    #[rr::requires("⌜i < length xs⌝")]
    #[rr::returns("#(xs !!! i)")]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        // TODO this is needed to force invariant unfolding before the shared borrow for self.ptr.
        self.len;
        unsafe {
            let p = RRPtr::mut_add(self.ptr(), index);
            let ret = &*p;
            ret
        }
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(fmap (M:=list) PlaceIn xs)", "Z.of_nat i")]
    #[rr::requires("⌜i < length xs⌝")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i))) else None")]
    pub fn get(&self, index: usize) -> Option<&T> {
        if (index < self.len()) {
            unsafe { Some (self.get_unchecked(index)) }
        }
        else {
            None
        }
    }
}
