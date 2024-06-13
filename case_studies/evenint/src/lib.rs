#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::include("option")]

#[rr::skip]
#[rr::returns("()")]
fn test() {
    let mut a;
    let b;
    unsafe {
        a = EvenInt::new(0);
        b = EvenInt::new(2);

        // broken!!
        let c = EvenInt::new(1);
    }

    //a.add_even(&b);
    assert!(a.get() % 2 == 0);
}

/*
fn get_even_int_from_user() -> Option<EvenInt> {
    let a = input(); 

    if a % 2 == 0 {
        Some(EvenInt::new(a))
    }
    else {
        None
    }
}
*/



#[rr::refined_by("x" : "Z")]
#[rr::invariant("Zeven x")]
struct EvenInt {
    #[rr::field("x")]
    num: i32,
}


impl EvenInt {
    #[rr::params("i" : "Z")]
    //#[rr::requires("i < MaxInt i32")]
    #[rr::args("i")] 
    #[rr::exists("j" : "Z")]
    #[rr::returns("j")]
    pub fn new_2(x: i32) -> Self {
        if x % 2 == 0 {
            Self {num: x}
        }
        else {
            if x < 1000 {
                Self { num : x + 1 } 
            }
            else {
                Self { num : x - 1 } 
            }
        }
    }

    #[rr::params("i" : "Z")]
    #[rr::args("i")] 
    #[rr::exists("j" : "option Z")]
    #[rr::returns("<#>@{option} j")]
    pub fn new_3(x: i32) -> Option<Self> {
        if x % 2 == 0 {
            let y = unsafe { Self::new(x) };
            Some(y)
        }
        else {
            None
        }
    }

    /// Create a new even integer.
    #[rr::params("i" : "Z")]
    #[rr::args("i")] 
    #[rr::requires("Zeven i")]
    #[rr::returns("i")]
    pub unsafe fn new(x: i32) -> Self {
        Self {num: x}
    }

    /// Internal function. Unsafely add 1, making the integer odd.
    #[rr::params("i", "γ")]
    #[rr::args(#raw "(# (-[ #i] : plist (λ X, place_rfn X) [_]), γ)")]
    #[rr::requires("(i+1 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "-[ #(i+1)] : plist (λ X, place_rfn X) [_]")]
    unsafe fn add(&mut self) {
        self.num += 1;
    }

    /// Get the even integer
    #[rr::params("z")]
    #[rr::args("#z")]
    #[rr::ensures("Zeven z")]
    #[rr::returns("z")]
    pub fn get(&self) -> i32 {
        self.num
    }

    /// This should always succeed.
    #[rr::params("z")]
    #[rr::args("#z")]
    pub fn check_invariant(&self) {
        assert!(self.get() % 2 == 0);
    }

    /// Add another even integer.
    #[rr::params("z", "y", "γ")]
    #[rr::args("(#z, γ)", "#y")]
    #[rr::requires("(z + y)%Z ∈ i32")]
    #[rr::observe("γ": "z + y")]
    pub fn add_even(&mut self, other: &EvenInt) {
        self.num += other.num;
    }

    /// Add 2 to an even integer.
    #[rr::params("z", "γ")]
    #[rr::args("(#z, γ)")]
    #[rr::requires("(z + 2 ≤ MaxInt i32)%Z")]
    #[rr::observe("γ": "z + 2")]
    pub fn add_two(&mut self) {
        self.num;

        unsafe {
            self.add();
            self.add();
        }
    }
}
