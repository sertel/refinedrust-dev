
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

#[rr::returns("()")]
fn test_add_2<T>(x: T, y: T) where T: MyAdd {
    MyAdd::my_add(x, y);
}
