
trait MyAdd {
    fn my_add(x: Self, y: Self) -> Self;
}

impl MyAdd for usize {
    #[rr::trust_me]
    #[rr::params("x", "y")]
    #[rr::args("x", "y")]
    #[rr::returns("x + y")]
    fn my_add(x: usize, y: usize) -> usize {
        x + y
    }
}

#[rr::returns("()")]
fn test_add() {
    MyAdd::my_add(5usize, 5usize);
}

// TODO: implement trait invocation for Param
#[rr::skip]
#[rr::returns("()")]
fn test_add_2<T>(x: T, y: T) where T: MyAdd {
    MyAdd::my_add(x, y);
}


pub trait Bla {
    type Output;

    fn bla(&self) -> &Self::Output;
}

impl<T> Bla for Option<T> {
    type Output = Option<T>;

    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("#x")]
    fn bla(&self) -> &Option<T> {
        self
    }
}

#[rr::returns("()")]
fn test_bla() {
    let x = Some(3);
    let bla = x.bla();
}
