extern crate crucible;
use crucible::*;

#[derive(Debug)]
#[repr(transparent)]
struct S {
    s1: u16,
}

#[crux::test]
fn crux_test() -> S {
    let s1 = u16::symbolic("s1");
    let s = S { s1 };

    crucible_assume!(s1 < 2);
    crucible_assume!(s1 > 0);

    concretize(s)
}

pub fn main() {
    println!("{:?}", crux_test());
}

