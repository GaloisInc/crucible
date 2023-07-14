extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> u8 {
    let x = u8::symbolic("\0:., /");
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
