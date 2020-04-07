extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;

fn test_one(i: u64) {
    let bv = Bv256::from(i);
    let j: u64 = bv.into();
    crucible_assert!(i == j);
}

#[crux_test]
fn crux_test() {
    test_one(0);
    test_one(1);
    test_one(12345);
}
