use std::mem;
extern crate crucible;
use crucible::*;

fn f(c: bool, t: i32, e: i32) -> i32 {
    if c { t } else { e }
}

#[cfg_attr(crux, crux_test)]
fn crux_test1() -> i32 {
    f(false, 1, 2)
}

#[cfg_attr(crux, crux_test)]
fn crux_test2() -> i32 {
    f(true, 10, 20)
}
