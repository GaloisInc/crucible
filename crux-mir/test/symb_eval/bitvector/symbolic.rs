#![feature(custom_attribute)]
extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;
use crucible::Symbolic;

#[crux_test]
fn crux_test() {
    {
        let a = Bv256::symbolic("a");
        crucible_assert!(a == a);
    }

    {
        let a = Bv256::symbolic("a");
        let b = Bv256::symbolic("b");
        crucible_assert!((u64::from(a) + u64::from(b)) == u64::from(a + b));
    }
}
