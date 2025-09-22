// A regression test for #1545, which ensures that crux-mir is able to
// concretize references to statics, i.e., references that are represented with
// GlobalVar_RefRoot under the hood.

extern crate crucible;
use crucible::*;

static X: u32 = 0;

#[crux::test]
pub fn f() -> u32 {
    *crucible::concretize(&X)
}
