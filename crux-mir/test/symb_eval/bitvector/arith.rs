#![feature(custom_attribute)]
extern crate crucible;
use crucible::bitvector::Bv256;
use crucible::crucible_assert;
use crucible::Symbolic;

use std::ops::{Not, Neg, Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};

fn test_unop(f: impl FnOnce(u64) -> u64, f_bv: impl FnOnce(Bv256) -> Bv256) {
    let a = u64::symbolic("a");
    let x = f_bv(Bv256::from(a));
    crucible_assert!(u64::from(x) == f(a));
}

fn test_binop_with(a: u64, b: u64, f: impl FnOnce(u64, u64) -> u64, f_bv: impl FnOnce(Bv256, Bv256) -> Bv256) {
    let x = f_bv(Bv256::from(a), Bv256::from(b));
    crucible_assert!(u64::from(x) == f(a, b));
}

fn test_binop(f: impl FnOnce(u64, u64) -> u64, f_bv: impl FnOnce(Bv256, Bv256) -> Bv256) {
    let a = u64::symbolic("a");
    let b = u64::symbolic("b");
    test_binop_with(a, b, f, f_bv);
}

fn test_shift_op(f: impl FnOnce(u64, usize) -> u64, f_bv: impl FnOnce(Bv256, usize) -> Bv256) {
    let a = u64::symbolic("a");
    let b = usize::symbolic("b");
    let x = f_bv(Bv256::from(a), b);
    crucible_assert!(u64::from(x) == f(a, b));
}

#[crux_test]
fn crux_test() {
    test_binop(Add::add, Add::add);
    test_binop(Sub::sub, Sub::sub);
    test_binop(BitAnd::bitand, BitAnd::bitand);
    test_binop(BitOr::bitor, BitOr::bitor);
    test_binop(BitXor::bitxor, BitXor::bitxor);
    test_binop(Mul::mul, Mul::mul);

    test_binop_with(10, 3, Div::div, Div::div);
    test_binop_with(10, 3, Rem::rem, Rem::rem);

    test_unop(Not::not, Not::not);

    test_shift_op(Shl::shl, Shl::shl);
    test_shift_op(Shr::shr, Shr::shr);
}
