extern crate crucible;
use crucible::*;

union U {
    u1: u16,
    u2: [u8; 2],
}

#[crux::test]
fn crux_test() -> [u8; 2] {
    let u2 = <[u8; 2]>::symbolic("u2");
    let u = U { u2 };

    crucible_assume!(u2[0] < 2);
    crucible_assume!(u2[1] < 2);
    crucible_assume!(u2[0] + u2[1] > 1);

    unsafe { concretize(u).u2 }
}

pub fn main() {
    println!("{:?}", crux_test());
}

