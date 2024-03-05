
#[repr(C)]
struct Pair<T, U> {
    x: T,
    y: U,
}

impl<T, U> Pair<T, U> {

    #[rr::params(x, y)]
    #[rr::args("x", "y")]
    #[rr::returns("-[#x; #y]")]
    pub fn new(x: T, y: U) -> Self {
        Self{x, y}
    }
}






#[rr::refined_by("x" : "Z")]
#[rr::invariant("Zeven x")]
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}

impl EvenInt {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::requires("Zeven x")]
    #[rr::returns("x")]
    pub fn new(x: i32) -> Self {
        Self {num: x}
    }

    #[rr::params("x", "γ")]
    #[rr::args(#raw "(#(-[#x]), γ)")]
    #[rr::requires("(x + 1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(-[#(x+1)%Z] : plist place_rfn _)")]
    fn add(&mut self) {
        self.num += 1;
    }

    #[rr::params("x", "γ", "y")]
    #[rr::args("(#x, γ)", "#y")]
    #[rr::requires("(x + y ∈ i32)%Z")]
    #[rr::observe("γ": "(x+y)")]
    #[rr::tactics("apply Zeven_plus_Zeven; solve_goal.")]
    pub fn add_even(&mut self, other: &Self) {
        self.num += other.num;
    }

    #[rr::params("x", "γ")]
    #[rr::args("(#x, γ)")]
    #[rr::requires("(x + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "(x+2)")]
    #[rr::tactics("rewrite -Z.add_assoc; apply Zeven_plus_Zeven; solve_goal.")]
    pub fn add_two(&mut self) {
        self.num;

        self.add();
        self.add();
    }
}



pub struct Foo {}

impl Foo {
    #[rr::params("x", "γ")]
    #[rr::args("(#x, γ)")]
    #[rr::returns("()")]
    pub fn a(&mut self) {
        assert!(true);
    }

    #[rr::params("x", "γ")]
    #[rr::args("(#x, γ)")]
    #[rr::returns("()")]
    pub fn b(&mut self) {
        assert!(true);
    }
}
