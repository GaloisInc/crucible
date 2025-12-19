extern crate crucible;
use crucible::*;

#[derive(Debug)]
enum E {
    E1(char),
    E2(u16, u16),
}

#[crux::test]
fn crux_test() -> E {
    let a = u16::symbolic("a");
    let b = u16::symbolic("b");
    let e = E::E2(a, b);

    crucible_assume!(a == 42);
    crucible_assume!(a == b);

    concretize(e)
}

pub fn main() {
    println!("{:?}", crux_test());
}

