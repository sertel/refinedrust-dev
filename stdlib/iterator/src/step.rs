#![rr::import("stdlib.iterator.theories", "step")]

#[rr::export_as(core::iter::Step)]
// TODO add support for using Self.
#[rr::context("Steppable {rt_of Self}")]
pub trait Step: Clone + PartialOrd + Sized {
    #[rr::args("#x", "#y")]
    #[rr::returns("")]
    fn steps_between(start: &Self, end: &Self) -> Option<usize>;

    fn forward_checked(start: Self, count: usize) -> Option<Self>;

    fn forward(start: Self, count: usize) -> Self {
        Step::forward_checked(start, count).expect("overflow in `Step::forward`")
    }

    unsafe fn forward_unchecked(start: Self, count: usize) -> Self {
        Step::forward(start, count)
    }

    fn backward_checked(start: Self, count: usize) -> Option<Self>;

    fn backward(start: Self, count: usize) -> Self {
        Step::backward_checked(start, count).expect("overflow in `Step::backward`")
    }

    unsafe fn backward_unchecked(start: Self, count: usize) -> Self {
        Step::backward(start, count)
    }
}

// TODO: we should implement Step for common integer types
// have a Coq reflection "Steppable" of Step and show an instance of that for Z.
// - abstracting to the refinement type and having something similar there seems like a common
// pattern for many traits.
