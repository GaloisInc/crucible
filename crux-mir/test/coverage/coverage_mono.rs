use std::mem;
extern crate crucible;
use crucible::*;

fn f<T>(c: bool, t: T, e: T) -> T {
    if c { t } else { e }
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    f::<u8>(false, 1_u8, 2_u8) as i32 + f::<i32>(true, 10, 20)
}
