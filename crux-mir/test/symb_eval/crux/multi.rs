
extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux::test)]
fn fail1() {
    let x = u8::symbolic("x");
    crucible_assert!(x + 1 > x);
}

#[cfg_attr(crux, crux::test)]
fn fail2() {
    let x = u8::symbolic("x");
    if x == 0 {
        panic!("one")
    }
}

fn assert_zero(x: u8) {
    crucible_assert!(x == 0);
}

#[cfg_attr(crux, crux::test)]
fn fail3() {
    let x = u8::symbolic("x");
    assert_zero(x);
}
