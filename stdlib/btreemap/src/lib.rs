#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.btreemap")]
#![rr::include("option")]
#![rr::include("alloc")]
#![allow(unused)]

#![feature(allocator_api)]

use std::alloc::{Allocator, Global};

use std::borrow::Borrow;
use std::cmp::Ord;

#[rr::export_as(alloc::collections::BTreeMap)]
#[rr::context("EqDecision {rt_of K}")]
#[rr::context("Countable {rt_of K}")]
#[rr::refined_by("M" : "gmap {rt_of K} (place_rfn {rt_of V})")]
#[rr::exists("k", "v", "a")]
pub struct BTreeMap<
    K,
    V,
    A: Allocator + Clone = Global,
> {
    #[rr::field("k")]
    _k: K,
    #[rr::field("v")]
    _v: V,
    #[rr::field("a")]
    _a: A,
}

#[rr::export_as(alloc::collections::BTreeMap)]
#[rr::context("EqDecision {rt_of K}")]
#[rr::context("Countable {rt_of K}")]
#[rr::only_spec]
impl<K, V> BTreeMap<K, V> {
    
    #[rr::returns("∅")]
    pub const fn new() -> BTreeMap<K, V> {
        unimplemented!();
    }


}

#[rr::context("EqDecision {rt_of K}")]
#[rr::context("Countable {rt_of K}")]
#[rr::export_as(alloc::collections::BTreeMap)]
impl<K, V, A: Allocator + Clone> BTreeMap<K, V, A> {

    #[rr::skip]
    #[rr::params("m", "k")]
    #[rr::args("#m", "#k")]
    // TODO: Borrow trait has two pure conversion functions between the refinement types
    #[rr::returns("<#>@{option} (m !! borrow_from k)")]
    pub fn get<Q>(&self, key: &Q) -> Option<&V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        unimplemented!(); 
    }

    #[rr::skip]
    #[rr::params("m", "k", "γ")]
    #[rr::args("(#m, γ)", "#k")]
    #[rr::exists("γi")]
    #[rr::returns("if decide (is_Some (m !! k)) then Some (m !!! k, γi) else None")]
    #[rr::observe("γ": "if decide (is_Some (m !! k)) then <[k := PlaceGhost γi]> m else m")]
    pub fn get_mut<Q: ?Sized>(&mut self, key: &Q) -> Option<&mut V>
    where
        K: Borrow<Q> + Ord,
        Q: Ord,
    {
        unimplemented!(); 
    }

    #[rr::only_spec]
    #[rr::params("m", "k", "v", "γ")]
    #[rr::args("(#m, γ)", "k", "v")]
    #[rr::observe("γ": "<[k := #v]> m")]
    #[rr::returns("(m !! k)")]
    pub fn insert(&mut self, key: K, value: V) -> Option<V>
    where
        K: Ord,
    {
        unimplemented!();
    }
}
