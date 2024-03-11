#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]
#![rr::coq_prefix("stdlib.option")]


#[rr::refined_by("option (place_rfn {rt_of T})")]
#[rr::export_as(core::option::Option)]
pub enum Option<T> {
    #[rr::pattern("None")]
    #[rr::export_as(core::option::Option::None)]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("-[x]")]
    #[rr::export_as(core::option::Option::Some)]
    Some(T)
}

#[rr::export_as(core::option::Option)]
#[rr::only_spec]
impl<T> Option<T> {

    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("bool_decide (is_Some x)")]
    pub fn is_some(&self) -> bool {
        unimplemented!();
    }

    #[rr::params("x")]
    #[rr::args("#x")]
    #[rr::returns("bool_decide (¬ is_Some x)")]
    pub fn is_none(&self) -> bool {
        unimplemented!()
    }

    #[rr::params("x")]
    #[rr::args("Some (#x)")]
    #[rr::returns("x")]
    pub fn unwrap(self) -> T {
        unimplemented!();
    }
}
