#![rr::import("refinedrust.extra_proofs.tests.enums", "enums")]

#[rr::refined_by("option (place_rfn {rt_of T})")]
enum Option<T> {
    #[rr::pattern("None")]
    None,
    #[rr::pattern("Some" $ "x")]
    #[rr::refinement("-[x]")]
    Some(T)
}

impl<T> Option<T> {
    #[rr::returns("None")]
    pub fn none() -> Self {
        Self::None
    }

    pub fn some(x : T) -> Self {
        Self::Some(x)
    }
}


#[rr::refined_by("result {rt_of T} {rt_of U}")]
enum Result<T, U> {
    #[rr::pattern("Ok" $ "x")]
    #[rr::refinement("-[#x]")]
    Ok(T),
    #[rr::pattern("Err" $ "x")]
    #[rr::refinement("-[#x]")]
    Err(U),
}

impl<T, U> Result<T, U> {
    #[rr::params("x")]
    #[rr::args("x")]
    pub fn foo(&self) {
    }
}

#[repr(u8)]
#[rr::refined_by("sizes")]
enum sizes {
    #[rr::pattern("Sz1")]
    Sz1 = 2,
    #[rr::pattern("Sz2")]
    Sz2,
}

impl sizes {
    #[rr::returns("Sz1")]
    pub fn new() -> Self {
        Self::Sz1
    }
}
