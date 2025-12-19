extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() -> (u8, u16, u32) {
    let a = u8::symbolic("a");
    let b = u16::symbolic("b");
    let c = u32::symbolic("c");

    crucible_assume!(a == 42);
    crucible_assume!(b as u8 == a);
    crucible_assume!(c as u16 == b);

    concretize((a, b, c))
}

pub fn main() {
    println!("{:?}", crux_test());
}

