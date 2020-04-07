extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;
use crucible::Symbolic;

#[crux_test]
fn crux_test() {
    let a = u64::symbolic("a");
    let b = u64::symbolic("b");
    let (c, o) = a.overflowing_sub(b);
    let bv_a = Bv256::from(a);
    let bv_b = Bv256::from(b);
    let (bv_c, bv_o) = bv_a.overflowing_sub(bv_b);
    crucible_assert!(u64::from(bv_c) == c);
    crucible_assert!(bv_o == o);
}
