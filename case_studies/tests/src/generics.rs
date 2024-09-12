
#[rr::params("x")]
#[rr::args("x")]
fn generic1<T>(x: T) {

}

#[rr::verify]
fn call_generic1_1() {
    generic1(42);
}

#[rr::verify]
fn call_generic1_2() {
    let x = 1;
    generic1(&x);
}

// TODO missing annotations to generate
#[rr::skip]
fn call_generic1_3() {
    let x = 1;
    let y = 2;
    generic1((&x, &y));
}

#[rr::params("x")]
#[rr::args("#x")]
fn generic2<'a, T>(x : &'a T) {

}

#[rr::verify]
fn call_generic2_1() {
    let x = 1;
    generic2(&x);
}

#[rr::params("x")]
#[rr::args("#x")]
fn generic3<'a>(x : &'a i32) {

}

#[rr::verify]
fn call_generic3_1() {
    let x = 1;
    generic3(&x);
}
