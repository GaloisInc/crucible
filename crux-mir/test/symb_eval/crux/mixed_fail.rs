#![feature(custom_attribute)]

extern crate crucible;
use crucible::*;

#[crux_test]
fn fail1() {
    let x = u8::symbolic("x");
    crucible_assert!(x + 1 > x);
}

#[crux_test]
fn fail2() {
    let x = u8::symbolic("x");
    crucible_assert!(x + 2 > x);
}

#[crux_test]
fn pass1() {
    let x = u8::symbolic("x");
    crucible_assert!(x > 10 || x <= 10);
}

#[crux_test]
fn pass2() {
    let x = u8::symbolic("x");
    crucible_assert!(x > 20 || x <= 20);
}
