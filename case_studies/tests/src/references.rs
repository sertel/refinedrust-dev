
#[rr::params("γ1", "γ2", "i")]
#[rr::args("(#(#i, γ1), γ2)")]
#[rr::observe("γ2": "(#i, γ1)")]
#[rr::returns("i")]
fn mut_ref_test1(x: &mut &mut i32) -> i32 {
    **x
}

#[rr::params("γ1", "γ2", "i", "j")]
#[rr::args("(#(-[#(#i, γ1); #j]), γ2)")]
#[rr::observe("γ2": "(-[#(#i, γ1); #j])")]
#[rr::returns("i")]
fn mut_ref_test2(x: &mut (&mut i32, i32)) -> i32 {
    *((*x).0)
}
