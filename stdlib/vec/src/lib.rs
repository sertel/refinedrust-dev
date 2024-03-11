#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::include("option")]
#![rr::include("alloc")]

#![feature(allocator_api)]
#![rr::coq_prefix("stdlib.alloc")]

use std::alloc::{Allocator, Global};


#[rr::refined_by("xs" : "list (place_rfn {rt_of T})")]
#[rr::exists("x", "y")]
#[rr::export_as(alloc::vec::Vec)]
pub struct Vec<T, A: Allocator = Global> {
    #[rr::field("x")]
    _x: T,
    #[rr::field("y")]
    _y: A,
}

#[rr::export_as(alloc::vec::Vec)]
#[rr::trust_me]
impl<T> Vec<T> {

    #[rr::returns("[]")]
    pub fn new() -> Self {
        unreachable!();
    }

}

#[rr::export_as(alloc::vec::Vec)]
#[rr::trust_me]
impl<T, A: Allocator> Vec<T, A> {

    #[rr::params("xs")]
    #[rr::args("#xs")]
    #[rr::returns("length xs")]
    pub fn len(&self) -> usize {
        unreachable!();
    }

    #[rr::params("xs", "γ", "x")]
    #[rr::args("(#xs, γ)", "x")]
    #[rr::requires("(length xs < max_int usize_t)%Z")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ max_int isize_t)%Z")]
    #[rr::observe("γ": "xs ++ [ #x]")]
    pub fn push(&mut self, elem: T) {
        unreachable!();
    }

    #[rr::params("xs", "γ")]
    #[rr::args("(#(<#>xs), γ)")]
    #[rr::returns("<#>@{option} (last xs)")]
    #[rr::observe("γ": "take (length xs - 1) (<#> xs)")]
    pub fn pop(&mut self) -> Option<T> {
        unreachable!();
    }

    #[rr::params("xs", "γ", "i" : "nat", "x")]
    #[rr::args("(#(<#>xs), γ)", "Z.of_nat i", "x")]
    #[rr::requires("i ≤ length xs")]
    #[rr::requires("(length xs < max_int usize_t)%Z")]
    #[rr::requires("(size_of_array_in_bytes {st_of T} (2 * length xs) ≤ max_int isize_t)%Z")]
    #[rr::observe("γ": "(<#> take i xs) ++ [ #x] ++ (<#> drop i xs)")]
    pub fn insert(&mut self, index: usize, elem: T) {
        unreachable!();
    }

    #[rr::params("xs", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::observe("γ": "delete i (<#> xs)")]
    pub fn remove(&mut self, index: usize) -> T {
        unreachable!(); 
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::exists("γi")]
    #[rr::returns("(#(xs !!! i), γi)")]
    #[rr::observe("γ": "<[i := PlaceGhost γi]> (<#> xs)")]
    pub unsafe fn get_unchecked_mut(&mut self, index: usize) -> &mut T {
        unreachable!(); 
    }

    #[rr::params("xs" : "list {rt_of T}", "γ", "i" : "nat")]
    #[rr::args("(#(<#> xs), γ)", "Z.of_nat i")]
    #[rr::exists("γi")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i), γi)) else None")]
    #[rr::observe("γ": "if decide (i < length xs) then <[i := PlaceGhost γi]> (<#> xs) else <#> xs")]
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        unreachable!(); 
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(<#> xs)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::returns("#(xs !!! i)")]
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        unreachable!(); 
    }

    #[rr::params("xs", "i" : "nat")]
    #[rr::args("#(<#> xs)", "Z.of_nat i")]
    #[rr::requires("i < length xs")]
    #[rr::returns("if decide (i < length xs) then Some (#(#(xs !!! i))) else None")]
    pub fn get(&self, index: usize) -> Option<&T> {
        unreachable!();
    }
}
