extern crate crucible;
use crucible::*;

#[crux_test]
fn crux_test() -> u8 {
    let s = if bool::symbolic("cond") { "a" } else { "b" };
    let x = u8::symbolic(s);
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
