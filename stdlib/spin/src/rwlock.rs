use std::ops::{Deref, DerefMut};
use crate::relax::*;


#[rr::export_as(spin::rwlock::RwLock)]
#[rr::refined_by("()" : "()")]
#[rr::exists("x", "y")]
pub struct RwLock<T, R = Spin> {
    #[rr::field("x")]
    _t : T,
    #[rr::field("y")]
    _r : R,
}

#[rr::export_as(spin::rwlock::RwLockReadGuard)]
#[rr::refined_by("x" : "{rt_of T}")]
pub struct RwLockReadGuard<'a, T: 'a> {
    #[rr::field("#x")]
    _t: &'a T,
}

#[rr::export_as(spin::rwlock::RwLockWriteGuard)]
#[rr::refined_by("x" : "place_rfn {rt_of T}")]
pub struct RwLockWriteGuard<'a, T: 'a, R = Spin> {
    #[rr::field("#()")]
    _l: &'a RwLock<T>,
    _r: R,
}


#[rr::export_as(spin::rwlock::RwLock)]
#[rr::only_spec]
impl<T, R> RwLock<T, R> {

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("()")]
    pub fn new(t: T) -> RwLock<T, R> {
        unimplemented!();
    }
}

impl<T, R: RelaxStrategy> RwLock<T, R> {

    // TODO: ensure the lock isn't already held by current thread (need to rule out panic).
    // For that, also need Drop.
    #[rr::skip]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    pub fn read(&self) -> RwLockReadGuard<T> {
        unimplemented!();
    }

    // TODO: ensure the lock isn't already held by current thread (need to rule out panic)
    // For that, also need Drop.
    #[rr::skip]
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::exists("y")]
    #[rr::returns("#y")]
    pub fn write(&self) -> RwLockWriteGuard<T, R> {
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
