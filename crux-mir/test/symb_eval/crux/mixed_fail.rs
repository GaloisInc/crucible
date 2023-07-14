
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
    crucible_assert!(x + 2 > x);
}

#[crux::test]
fn pass1() {
    let x = u8::symbolic("x");
    crucible_assert!(x > 10 || x <= 10);
}

#[crux::test]
fn pass2() {
    let x = u8::symbolic("x");
    crucible_assert!(x > 20 || x <= 20);
}
