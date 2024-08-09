
const NUM_BLA: i32 = 1024;

#[rr::params("a")]
#[rr::args("a")]
#[rr::returns("2048")]
const fn compute_bla(a : i32) -> i32 {
    let _y = a;
    let x = NUM_BLA * 2;
    x
}

const RESULT_BLA: i32 = compute_bla(30);

#[rr::returns("2048")]
fn use_result() -> i32{
    let x = RESULT_BLA;
    x
}

#[rr::params("x")]
#[rr::args("#x")]
#[rr::returns("()")]
fn use_ref(x: &i32) {

}

// TODO: need to support GlobalAlloc evaluation
#[rr::skip]
#[rr::returns("()")]
fn call_with_const_ref() {
    use_ref(&42)
}
