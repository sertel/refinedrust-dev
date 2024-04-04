#![rr::include("option")]

#[rr::name("MYINT")]
static MYINT: i32 = 42;

#[rr::requires(#iris "initialized π \"MYINT\" 42")]
#[rr::returns("42")]
fn read_static_1() -> i32 {
    MYINT
}

#[rr::params("x")]
#[rr::requires(#iris "initialized π \"MYINT\" x")]
#[rr::returns("#x")]
fn ref_static_1() -> &'static i32 {
    &MYINT
}

#[rr::requires(#iris "initialized π \"MYINT\" 42")]
#[rr::returns("()")]
fn read_static_2() {
    let r = ref_static_1();
    let _ = *r;
}

// TODO
#[rr::skip]
#[rr::params("x")]
#[rr::requires(#iris "initialized π \"MYINT\" x")]
#[rr::returns("Some(#(#x))")]
fn ref_static_2() -> Option<&'static i32> {
    Some(&MYINT)
}

// TODO: need to properly put lifetimes instead of placeholder_lft
#[rr::skip]
#[rr::requires(#iris "initialized π \"MYINT\" 42")]
#[rr::returns("()")]
fn read_static_3() {
    let r = ref_static_2();
    let r2 = r.unwrap();
    let _ = *r2;
}
