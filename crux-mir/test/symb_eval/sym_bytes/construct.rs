extern crate crucible;
use crucible::*;
use crucible::sym_bytes::SymBytes;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u8 {
    let sym1 = SymBytes::zeroed(5);
    // Should succeed - sym1[0] is zero.  In fact, this should get simplified away and not produce
    // a solver goal at all.
    crucible_assert!(sym1[0] == 0);
    let sym2 = SymBytes::symbolic("sym", 5);
    // Should fail - sym2[0] is arbitrary
    crucible_assert!(sym2[0] == 0);
    sym1[0] + sym2[0]
}

pub fn main() {
    println!("{:?}", crux_test());
}
