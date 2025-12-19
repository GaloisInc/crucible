extern crate crucible;
use crucible::*;

#[derive(Debug)]
struct S {
    s1: u16,
    s2: u16,
}

#[crux::test]
fn crux_test() -> S {
    let s1 = u16::symbolic("s1");
    let s2 = u16::symbolic("s2");
    let s = S { s1, s2 };

    crucible_assume!(s1 < 2);
    crucible_assume!(s2 < 2);
    crucible_assume!(s1 + s2 > 1);

    concretize(s)
}

pub fn main() {
    println!("{:?}", crux_test());
}

