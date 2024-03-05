use crate::*;

#[rr::returns("()")]
fn get_mut_client() {

    // We have desugared this, as the macro uses parts of Rust our frontend does not support yet.
    //let mut x = vec![100, 200, 300];
    let mut x = Vec::new();
    x.push(100);
    x.push(200);
    x.push(300);

    let xr = x.get_mut(1).unwrap();
    assert!(*xr == 200);
    *xr = 42;
    assert!(*x.get_mut(1).unwrap() == 42);
}
