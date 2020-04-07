extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;
use crucible::Symbolic;

#[crux_test]
fn crux_test() {
    {
        let (a, b) = <(u64, u64)>::symbolic("ab");
        crucible_assert!((Bv256::from(a) == Bv256::from(b)) == (a == b));
    }

    {
        let (a, b) = <(u64, u64)>::symbolic("ab");
        crucible_assert!((Bv256::from(a) < Bv256::from(b)) == (a < b));
    }
}
