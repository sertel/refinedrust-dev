
#![feature(register_tool)]
#![register_tool(rr)]
#![feature(custom_inner_attributes)]

#![rr::package("refinedrust-stdlib")]
#![rr::coq_prefix("stdlib.controlflow")]
#![allow(unused)]

#[rr::refined_by("sum (place_rfn {rt_of C}) (place_rfn {rt_of B})")]
#[rr::export_as(core::ops::ControlFlow)]
pub enum ControlFlow<B, C = ()> {
    #[rr::pattern("inl" $ "x")]
    #[rr::refinement("-[x]")]
    #[rr::export_as(core::ops::ControlFlow::Continue)]
    Continue(C),
    /// Exit the operation without running subsequent phases.
    #[rr::pattern("inr" $ "x")]
    #[rr::refinement("-[x]")]
    #[rr::export_as(core::ops::ControlFlow::Break)]
    Break(B),
}

#[rr::export_as(core::ops::Try)]
pub trait Try: FromResidual {
    /// The type of the value produced by `?` when *not* short-circuiting.
    type Output;

    /// The type of the value passed to [`FromResidual::from_residual`]
    /// as part of `?` when short-circuiting.
    ///
    /// This represents the possible values of the `Self` type which are *not*
    /// represented by the `Output` type.
    type Residual;

    /// Constructs the type from its `Output` type.
    ///
    /// This should be implemented consistently with the `branch` method
    /// such that applying the `?` operator will get back the original value:
    /// `Try::from_output(x).branch() --> ControlFlow::Continue(x)`.
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn from_output(output: Self::Output) -> Self;

    /// Used in `?` to decide whether the operator should produce a value
    /// (because this returned [`ControlFlow::Continue`])
    /// or propagate a value back to the caller
    /// (because this returned [`ControlFlow::Break`]).
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::exists("y")]
    #[rr::returns("y")]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output>;
}

#[rr::export_as(core::ops::FromResidual)]
pub trait FromResidual<R = <Self as Try>::Residual> {
    /// Constructs the type from a compatible `Residual` type.
    ///
    /// This should be implemented consistently with the `branch` method such
    /// that applying the `?` operator will get back an equivalent residual:
    /// `FromResidual::from_residual(r).branch() --> ControlFlow::Break(r)`.
    /// (It must not be an *identical* residual when interconversion is involved.)
    fn from_residual(residual: R) -> Self;
}

#[rr::export_as(core::convert::Infallible)]
#[rr::refined_by("()")]
pub enum Infallible {
    // In the model, we put a constructor, whereas the real type does not have a constructor.
    // This should be fine.
    #[rr::pattern("tt")]
    #[rr::refinement("-[]")]
    I
}

#[rr::only_spec]
#[rr::export]
impl<T> Try for Option<T> {
    type Output = T;
    type Residual = Option<Infallible>;

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("Some(#x)")]
    fn from_output(output: Self::Output) -> Self {
        Some(output)
    }

    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("match x with | Some(x) => inl(x) | None => inr(#None) end")]
    fn branch(self) -> ControlFlow<Self::Residual, Self::Output> {
        match self {
            Some(v) => ControlFlow::Continue(v),
            None => ControlFlow::Break(None),
        }
    }
}

#[rr::only_spec]
impl<T> FromResidual for Option<T> {
    #[rr::params("x")]
    #[rr::args("x")]
    #[rr::returns("None")]
    fn from_residual(residual: Option<Infallible>) -> Self {
        None
    }
}
