//! A test case to exercise conditional concretization of references to global
//! variables.

extern crate crucible;
use crucible::*;

static X: u8 = 42;

#[crux::test]
fn crux_test() {
    if bool::symbolic("b") {
        concretize(&X);
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
