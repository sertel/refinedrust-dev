#![rr::import("refinedrust.extra_proofs.tests.enums", "typing")]

enum Option<T> {
    None,
    Some(T)
}

impl<T> Option<T> {
    pub fn none() -> Self {
        Self::None
    }

    pub fn some(x : T) -> Self {
        Self::Some(x)
    }
}

#[repr(u8)]
#[rr::refined_by("sizes")]
enum sizes {
    #[rr::pattern("Sz1")]
    #[rr::variant("()")]
    Sz1 = 2,
    #[rr::pattern("Sz2")]
    #[rr::variant("()")]
    Sz2,
}

impl sizes {
    #[rr::returns("Sz1")]
    pub fn new() -> Self {
        Self::Sz1
    }
}
