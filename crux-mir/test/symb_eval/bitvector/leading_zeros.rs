extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::{crucible_assert, crucible_assume};
use crucible::Symbolic;

use std::ops::{Not, Neg, Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    {
        let a_64 = u64::symbolic("a");
        let a_256 = Bv256::from(a_64);
        crucible_assert!(a_256.leading_zeros() == (256 - 64) + a_64.leading_zeros());
    }

    {
        let b_64 = u64::symbolic("b");
        crucible_assume!(b_64 != 0);
        let b_256 = Bv256::from(b_64) << (256 - 64);
        crucible_assert!(b_256.leading_zeros() == b_64.leading_zeros());
    }
}
