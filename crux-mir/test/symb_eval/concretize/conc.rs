extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> (u8, u8) {
    let mut x = u8::symbolic("x");
    let mut y = u8::symbolic("y");
    crucible_assume!(x < 100 && y < 100);   // prevent overflow in addition
    crucible_assume!(x + y == 1);
    crucible_assume!(x != 0);
    let (x, y) = concretize((x, y));
    crucible_assert!(x == 0 || x == 1);
    crucible_assert!(y == 0 || y == 1);
    (x, y)
}

pub fn main() {
    println!("{:?}", crux_test());
}

