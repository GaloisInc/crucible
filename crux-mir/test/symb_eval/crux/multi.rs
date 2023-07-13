
extern crate crucible;
use crucible::*;

#[crux::test]
fn fail1() {
    let x = u8::symbolic("x");
    crucible_assert!(x + 1 > x);
}

#[crux::test]
fn fail2() {
    let x = u8::symbolic("x");
    if x == 0 {
        panic!("one")
    }
}

fn assert_zero(x: u8) {
    crucible_assert!(x == 0);
}

#[crux::test]
fn fail3() {
    let x = u8::symbolic("x");
    assert_zero(x);
}
