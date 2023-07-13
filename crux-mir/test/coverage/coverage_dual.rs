use std::mem;
extern crate crucible;
use crucible::*;

fn f(c: bool, t: i32, e: i32) -> i32 {
    if c { t } else { e }
}

#[crux::test]
fn crux_test1() -> i32 {
    f(false, 1, 2)
}

#[crux::test]
fn crux_test2() -> i32 {
    f(true, 10, 20)
}
