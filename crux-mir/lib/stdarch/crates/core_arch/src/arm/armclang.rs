//! ARM compiler specific intrinsics
//!
//! # References
//!
//! - [ARM Compiler v 6.10 - armclang Reference Guide][arm_comp_ref]
//!
//! [arm_comp_ref]: https://developer.arm.com/docs/100067/0610

#[cfg(test)]
use stdarch_test::assert_instr;

/// Inserts a breakpoint instruction.
///
/// `VAL` is a compile-time constant integer in range `[0, 255]`.
///
/// The breakpoint instruction inserted is `BKPT` on A32/T32.
///
/// # Note
///
/// [ARM's documentation][arm_docs] defines that `__breakpoint` accepts the
/// following values for `VAL`:
///
/// - `0...65535` when compiling as A32,
/// - `0...255` when compiling as T32.
///
/// The current implementation only accepts values in range `[0, 255]`.
///
/// [arm_docs]: https://developer.arm.com/docs/100067/latest/compiler-specific-intrinsics/__breakpoint-intrinsic
#[cfg_attr(test, assert_instr(bkpt, VAL = 0))]
#[inline(always)]
#[rustc_legacy_const_generics(0)]
pub unsafe fn __breakpoint<const VAL: i32>() {
    static_assert_imm8!(VAL);
    crate::arch::asm!("bkpt #{}", const VAL);
}
