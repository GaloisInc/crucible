extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> u8 {
    let mut x = u8::symbolic("x");
    let mut y = u8::symbolic("y");
    crucible_assume!(x.wrapping_add(y) == 1);
    if x > 1 { crucible_assume!(x == 100) }
    crucible_assert!(x == 0 || x == 1, "{} + {} == {}", x, y, x.wrapping_add(y));
    concretize(x.wrapping_add(y))
}

pub fn main() {
    println!("{:?}", crux_test());
}

