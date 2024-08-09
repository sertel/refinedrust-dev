#![rr::include("option")]
//#![rr::include("controlflow")]


#[rr::returns("Some (#2)")]
fn maybe_fails() -> Option<i32> {
    Some(2)
}

// TODO
#[rr::skip]
//#[rr::trust_me]
#[rr::returns("Some (#4)")]
fn get_result() -> Option<i32> {
    let x = maybe_fails()?;
    let y = maybe_fails()?;

    Some(x + y)
}
