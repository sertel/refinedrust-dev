#![allow(unused)]
#![rr::include("closures")]

#[rr::params("x")]
#[rr::args("x")]
fn closure_test_arg1<T>(x: T) 
    where T: FnOnce()
{
    x() 
}

#[rr::params("x")]
#[rr::args("x")]
fn closure_test_arg2<T>(x: T) 
    where T: FnOnce(i32) -> i32
{
    let r = x(42);
}

#[rr::returns("()")]
fn closure_test1() {

    // Fn-closure
    let x =
        #[rr::params("i")]
        #[rr::args("i")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        #[rr::returns("(2 * i)%Z")]
        |x: i32| {
            x * 2
        };

    // here we call the closure's implementation
    //x(2);
}

#[rr::returns("()")]
fn closure_test12() {

    // Fn-closure
    let x =
        #[rr::params("i", "j")]
        #[rr::args("i", "j")]
        #[rr::requires("(j * i)%Z ∈ i32")]
        #[rr::returns("(j * i)%Z")]
        |x: i32, y: i32| {
            x * y
        };

    // here we call the closure's implementation
    //x(2, 2);
}

#[rr::returns("()")]
fn closure_test5() {
    let x = 5;

    // Fn-closure
    let x =
        #[rr::params("i")]
        #[rr::capture("x": "i")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        #[rr::returns("(2 * i)%Z")]
        || {
            x * 2
        };

    // here we call the closure's implementation
    //x(2);
}

/*
#[rr::params("x")]
#[rr::args("#x")]
#[rr::returns("()")]
fn closure_test6(z: &i32) {
    let x = 5;

    // Fn-closure
    let x =
        #[rr::params("i", "j")]
        #[rr::capture("x": "i")]
        #[rr::capture("z": "j")]
        #[rr::requires("(j * i)%Z ∈ i32")]
        #[rr::returns("(j * i)%Z")]
        || {
            x * z
        };

    // here we call the closure's implementation
    //x(2);
}
*/

#[rr::returns("()")]
fn closure_test2() {
    let mut y = 2;

    // here, we prove initialization of the closure

    let mut x =
        // Note: the closure code has a doubly-nested mutable references, since it gets a mutref to
        // the capture also.
        #[rr::params("i")]
        #[rr::capture("y": "i" -> "(2*i)%Z")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        || { y *= 2; };

    //x();
    //x();

    // here, we deinitialize the closure
    y = y + 1;
}

#[rr::params("a", "γ")]
#[rr::args("(#a, γ)")]
#[rr::requires("(4*a)%Z ∈ i32")]
//#[rr::observe("γ" : "(4 * a)%Z")]
#[rr::observe("γ" : "a")]
#[rr::returns("()")]
#[rr::tactics("unsafe_unfold_common_caesium_defs; solve_goal.")]
fn closure_test3(y: &mut i32) {
    let mut z = 5;
    let mut yy = 423;

    let mut x =
        // this effectively takes a mutable reference for initialization
        #[rr::params("i", "j")]
        // TODO: we should specify the projection here.
        #[rr::capture("y" : "i" -> "2*i")]
        #[rr::capture("z" : "j" -> "5*j")]
        #[rr::requires("(2 * i)%Z ∈ i32")]
        #[rr::requires("(5 * j)%Z ∈ i32")]
        || { *y *= 2; z *= 5; };

    //x();
    //x();
}

/*
#[rr::returns("()")]
fn closure_test4(y: &mut i32) {
    let mut z = 5;

    let mut x =
        // this effectively takes a mutable reference for initialization
        #[rr::params("i", "γ", "j", "γj")]
        #[rr::capture_pre("y" : "(i, γ)")]
        #[rr::capture_pre("z" : "(j, γj)")]
        #[rr::capture_post("y" : "(2*i, γ)")]
        #[rr::capture_post("z" : "(5*i, γj)")]
        |x: &mut i32, w: &mut i32| { *y *= z; *x *= *w; };
}
*/

fn closure_test6<T>(x: T) {
    let cls = 
        #[rr::params("a")]
        #[rr::args("a")]
        #[rr::returns("a")]
        |a: T| { a };

    //cls(x);
}

fn closure_test7<T, U>(x: T, y: U) 
    where U: FnOnce(T)
{
    let cls = 
        #[rr::params("a", "m")]
        #[rr::capture("y": "m")]
        #[rr::args("a")]
        |a: T| { y(a) };

    //cls(x);
}

fn closure_test8<T, U>(x: T, y: U) 
    where U: FnOnce(T)
{
    let cls = 
        #[rr::params("a", "w")]
        #[rr::args("a", "w")]
        |a: T, w: U| { w(a) };

    //cls(x, y);
}

mod fncoercion {
    fn bla(b: bool) {
        let x = |x: i32| {x };
        // uses ClosureFnPointer coercion to coerce whichever closure we pick to an fn pointer
        // (because there are no captures)
        let z = if b { x } else { |x : i32| { x } };
        // then we use the closure instance for fn pointers
        blub(z);
    }

    fn blub<T>(mut x : T) where T: Fn(i32) -> i32 {
        x(43);
    }
}

// Note: probably I could try to have a more creusot-like language that compiles down to this
// representation
