extern crate crucible;
use crucible::*;

enum E {
    A = 10,
    B = 20,
    C = 30,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = u8::symbolic("x");
    crucible_assume!(x != 1);
    let e = match x {
        0 => E::A,
        1 => E::B,
        2 => E::C,
        _ => crucible_assume_unreachable!(),
    };

    let y = match e {
        E::A => 1,
        E::B => 2,
        E::C => 3,
    };
    y
}
