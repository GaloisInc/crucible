
extern crate crucible;
use crucible::*;

// The naive implementation that simply invokes `fail1(); fail2();` will produce only one panic,
// because `fail1` panics (terminating execution) on all branches and `fail2` never runs.  The
// desired behavior is to run both `fail1` and `fail2` and report their errors independently.

#[crux::test]
fn fail1() {
    panic!("bad 1");
}

#[crux::test]
fn fail2() {
    let x = u8::symbolic("x");
    crucible_assert!(x == 0);
}
