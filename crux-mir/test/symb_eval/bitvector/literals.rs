extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    crucible_assert!(u64::from(Bv256::ZERO) == 0);
    crucible_assert!(u64::from(Bv256::ONE) == 1);
}
