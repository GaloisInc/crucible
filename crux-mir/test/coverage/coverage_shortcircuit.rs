extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let x = u8::symbolic("x");
    crucible_assume!(x < 1);
    let mut y = 1;
    if x == 0 || x == 1 {
        y += 1;
    } else {
        y += 3;
    }
    y
}
