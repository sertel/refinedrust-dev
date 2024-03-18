
#[rr::name("MYINT")]
static MYINT: i32 = 42;

#[rr::requires(#iris "initialized π \"MYINT\" 42")]
#[rr::returns("42")]
fn read_static_1() -> i32 {
    MYINT
}
