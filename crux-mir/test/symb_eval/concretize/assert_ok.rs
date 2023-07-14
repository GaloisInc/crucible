extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> u8 {
    let mut x = u8::symbolic("x");
    let mut y = u8::symbolic("y");
    crucible_assume!(x < 100 && y < 100);
    crucible_assume!(x + y == 1);
    crucible_assert!(x == 0 || x == 1, "{} + {} == {}", x, y, x + y);
    concretize(x + y)
}

pub fn main() {
    println!("{:?}", crux_test());
}

