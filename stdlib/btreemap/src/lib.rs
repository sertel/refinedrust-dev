#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::include("option")]
#![rr::include("alloc")]

#![feature(allocator_api)]

use std::alloc::{Allocator, Global};

use std::borrow::Borrow;
use std::cmp::Ord;

#[rr::context("Countable {rt_of K}")]
#[rr::refined_by("M" : "gmap {rt_of K} {rt_of V}")]
pub struct BTreeMap<
    K,
    V,
    A: Allocator + Clone = Global,
> {
    _k: K,
    _v: V,
    _a: A,
}


#[rr::context("Countable {rt_of K}")]
impl<K, V> BTreeMap<K, V> {
    
    #[rr::returns("∅")]
    pub const fn new() -> BTreeMap<K, V> {
        unimplemented!();
    }


}

#[rr::context("Countable {rt_of K}")]
impl<K, V, A: Allocator + Clone> BTreeMap<K, V, A> {

    
    #[rr::args("#m", "#k")]
    // TODO: Borrow trait has two pure conversion functions between the refinement types
    #[rr::returns("<#>@{option} <#>@{option} (m !! borrow_from k)")]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        unimplemented!(); 
    }

    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        unimplemented!(); 
    }

    #[rr::args("(#m, γ)", "k", "v")]
    #[rr::observe("γ": "<[k := v]> m")]
    #[rr::returns("<#>@{option} (m !! k)")]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        unimplemented!();
    }
}
