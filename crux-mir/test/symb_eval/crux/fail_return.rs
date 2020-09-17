
extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn fail1() -> u8 {
    let x = u8::symbolic("x");
    crucible_assert!(x + 1 > x);
    x
}

#[cfg_attr(crux, crux_test)]
fn fail2() -> u8 {
    let x = u8::symbolic("x");
    crucible_assert!(x + 1 > x);
    123
}

