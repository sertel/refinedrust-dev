#![rr::include("vec")]
use std::vec::Vec;

#[rr::returns("()")]
fn init_vec() {
    let mut v: Vec<i32> = Vec::new();

    v.push(42);
    v.pop();

}
