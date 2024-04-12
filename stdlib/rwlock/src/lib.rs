#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.rwlock")]
#![allow(unused)]

use std::ops::{Deref, DerefMut};

#[rr::export_as(std::sync::poison::LockResult)]
pub type LockResult<Guard> = Result<Guard, PoisonError<Guard>>;

#[rr::export_as(std::sync::poison::PoisonError)]
#[rr::refined_by("()" : "()")]
#[rr::exists("x")]
pub struct PoisonError<T> {
    #[rr::field("x")]
    guard: T,
}

#[rr::export_as(std::sync::rwlock::RwLock)]
#[rr::refined_by("()" : "()")]
#[rr::exists("x")]
pub struct RwLock<T> {
    #[rr::field("x")]
    _t : T, 
}

#[rr::export_as(std::sync::rwlock::RwLockReadGuard)]
#[rr::refined_by("x" : "{rt_of T}")]
pub struct RwLockReadGuard<'a, T: 'a> {
    #[rr::field("#x")]
    _t: &'a T,
}

#[rr::export_as(std::sync::rwlock::RwLockWriteGuard)]
#[rr::refined_by("x" : "place_rfn {rt_of T}")]
pub struct RwLockWriteGuard<'a, T: 'a> {
    #[rr::field("#()")]
    _l: &'a RwLock<T>,
}


#[rr::export_as(std::sync::rwlock::RwLock)]
#[rr::only_spec]
impl<T> RwLock<T> {

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("()")]
    pub fn new(t: T) -> RwLock<T> {
        unimplemented!();
    }

    // TODO: ensure the lock isn't already held by current thread (need to rule out panic).
    // For that, also need Drop.
    #[rr::skip]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::exists("y" : "sum (place_rfn {rt_of T}) _")]
    #[rr::returns("y")]
    pub fn read(&self) -> LockResult<RwLockReadGuard<'_, T>> {
        unimplemented!();
    }

    // TODO: ensure the lock isn't already held by current thread (need to rule out panic)
    // For that, also need Drop.
    #[rr::skip]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::exists("y" : "sum (place_rfn {rt_of T}) _")]
    #[rr::returns("map_inl (#) y")]
    pub fn write(&self) -> LockResult<RwLockWriteGuard<'_, T>> {
        unimplemented!();
    }
}

#[rr::only_spec]
impl<T> Deref for RwLockWriteGuard<'_, T> {
    type Target = T;

    #[rr::skip]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("#x")]
    fn deref(&self) -> &T {
        unimplemented!(); 
    }
}

#[rr::only_spec]
impl<T> DerefMut for RwLockWriteGuard<'_, T> {

    #[rr::skip]
    #[rr::params("x" : "{rt_of T}")]
    #[rr::args("(#(#x), γ)")]
    #[rr::exists("γi")]
    #[rr::returns("(#x, γi)")]
    #[rr::observe("γ": "PlaceGhost γi")]
    fn deref_mut(&mut self) -> &mut T {
        unimplemented!();
    }
}
