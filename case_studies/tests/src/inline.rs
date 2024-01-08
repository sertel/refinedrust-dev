#[rr::inlined]
fn fct_inlined_add(x: i32, y: i32) -> i32 {
    x + y
}

#[rr::params(x : "Z")]
#[rr::args("x")]
#[rr::requires("(x + 42 ≤ MaxInt i32)%Z")]
#[rr::returns("x + 42")]
fn fct_inlined_add_42(x: i32) -> i32 {
    fct_inlined_add(x, 42)
}
