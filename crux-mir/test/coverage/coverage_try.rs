use std::convert::TryInto;
extern crate crucible;
use crucible::*;

fn f() -> Option<u8> {
    let x_32 = u32::symbolic("x");
    let x: u8 = x_32.try_into().ok()?;
    let y_32 = u32::symbolic("y");
    crucible_assume!(y_32 < 256);
    let y: u8 = y_32.try_into().ok()?;
    x.checked_add(y)
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u8 {
    f().unwrap_or(0)
}
