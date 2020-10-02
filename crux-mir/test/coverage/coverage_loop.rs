extern crate crucible;
use crucible::*;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut y = 1;
    for i in 0..10 {
        if i == 0 {
            y += 1;
        } else if i < 3 {
            y += 2;
        } else if i > 99 {
            y += 3;
        } else {
            y += 4;
        }
    }
    y
}
