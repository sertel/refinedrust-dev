
#[rr::params("c")]
#[rr::args("c")]
fn take_char(_c: char) {

}

#[rr::returns("()")]
fn make_char() {
    let _x = 'a';
}
