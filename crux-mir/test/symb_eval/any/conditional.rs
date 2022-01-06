//! Regression test for `Any`-typed locals under a symbolic branch.  Previously, this would mux the
//! assigned value with the default value produced by `initialValue`, causing an error ("Attempted
//! to mux ANY values of different runtime type").  Now `Any` no longer has a default value, so the
//! error no longer occurs.
#![feature(crucible_intrinsics)]
extern crate crucible;
use crucible::*;
use crucible::any::Any;

#[crux_test]
fn crux_test() {
    let mut x = bool::symbolic("x");
    if x {
        let y = Any::new(1);
    }
}
