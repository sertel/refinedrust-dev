#![rr::include("vec")]
#![rr::include("alloc")]
#![rr::include("option")]


use std::vec::Vec;

#[rr::skip]
#[rr::returns("()")]
fn init_vec() {
    let mut v: Vec<i32> = Vec::new();

    v.push(42);
    v.pop();

}
