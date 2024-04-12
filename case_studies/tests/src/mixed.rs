#![allow(unused)]

#[macro_export]
macro_rules! rr_stop {
    ( ) => {
        #[allow(unused_variables)] 
        let _  = #[rr::ignore] || {};
    };
}

#[rr::returns("()")]
fn test_mixed() {
    let mut x = 4;
    //rr_stop!();
    let mut y = 5;
    x = 10;
    //rr_stop!();
    y = 20;
}
