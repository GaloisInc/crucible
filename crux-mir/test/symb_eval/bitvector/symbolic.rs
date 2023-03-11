extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;
use crucible::Symbolic;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    {
        let a = Bv256::symbolic("a");
        crucible_assert!(a == a);
    }

    {
        let a = Bv256::symbolic("a");
        let b = Bv256::symbolic("b");
        // Bv256 addition is always wrapping.
        crucible_assert!((u64::from(a).wrapping_add(u64::from(b))) == u64::from(a + b));
    }
}
