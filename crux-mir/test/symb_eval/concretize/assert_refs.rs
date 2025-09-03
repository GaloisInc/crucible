// A regression test for #1513. This test ensures that crux-mir can
// successfully pass reference types (or types that use references under the
// hood, like Vecs) to the crucible_assert! macro.

extern crate crucible;
use crucible::*;

#[crux::test]
fn crux_test() {
    let x: u32 = 42;
    let v: Vec<u32> = vec![x];
    crucible_assert!(false, "{:?} {:?} {:?} {:?}", &x, &&x, v, &v);
}

pub fn main() {
    println!("{:?}", crux_test());
}
