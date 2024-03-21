#![rr::include("option")]

pub trait Bla {
    fn bla(&self);
}

impl<T> Bla for Option<T> {
    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("()")]
    fn bla(&self) {

    }
}

#[rr::returns("()")]
fn test_bla() {
    let x = Some(3);
    x.bla();
}


/*
#[rr::returns("Some (#2)")]
fn maybe_fails() -> Option<i32> {
    Some(2)
}

#[rr::returns("Some (#2)")]
fn get_result() -> Option<i32> {
    let x = maybe_fails()?;
    //let y = maybe_fails()?;

    Some(x)
}
*/
