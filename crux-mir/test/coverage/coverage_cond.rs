use std::convert::TryFrom;
extern crate crucible;
use crucible::*;

fn f(cond: bool) -> u8 {
    if cond { 10 } else { 20 }
}

fn g(cond: bool) -> u8 {
    if !cond { 10 } else { 20 }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u8 {
    f(true) + g(true)
}
