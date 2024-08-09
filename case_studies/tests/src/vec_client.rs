#![rr::include("vec")]
#![rr::include("alloc")]
#![rr::include("option")]


use std::vec::Vec;

#[rr::returns("()")]
fn init_vec() {
    let mut v: Vec<i32> = Vec::new();

    v.push(42);
    assert!(v.pop().unwrap() == 42);
}
