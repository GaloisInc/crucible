extern crate crucible;
use crucible::*;

fn f() -> i32 { 1 }
fn g() -> i32 { 2 }

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    crucible_assert!(f() == 1);
    crucible::override_(f, g);
    crucible_assert!(f() == 2);
}
