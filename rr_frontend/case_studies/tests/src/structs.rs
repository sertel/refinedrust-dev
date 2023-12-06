
#[repr(C)]
struct Pair<T, U> {
    x: T,
    y: U,
}

impl<T, U> Pair<T, U> {

    #[rr::params(x, y)]
    #[rr::args("x", "y")]
    #[rr::returns("+[#x; #y]")]
    pub fn new(x: T, y: U) -> Self {
        Self{x, y}
    }
}
