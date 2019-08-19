//! ARM intrinsics.
//!
//! The reference for NEON is [ARM's NEON Intrinsics Reference][arm_ref]. The
//! [ARM's NEON Intrinsics Online Database][arm_dat] is also useful.
//!
//! [arm_ref]: http://infocenter.arm.com/help/topic/com.arm.doc.ihi0073a/IHI0073A_arm_neon_intrinsics_ref.pdf
//! [arm_dat]: https://developer.arm.com/technologies/neon/intrinsics
#![allow(non_camel_case_types)]

mod armclang;

pub use self::armclang::*;

mod v6;
pub use self::v6::*;

#[cfg(any(target_arch = "aarch64", target_feature = "v7"))]
mod v7;
#[cfg(any(target_arch = "aarch64", target_feature = "v7"))]
pub use self::v7::*;

// NEON is supported on AArch64, and on ARM when built with the v7 and neon
// features. Building ARM without neon produces incorrect codegen.
#[cfg(any(
    target_arch = "aarch64",
    all(target_feature = "v7", target_feature = "neon"),
    dox
))]
mod neon;
#[cfg(any(
    target_arch = "aarch64",
    all(target_feature = "v7", target_feature = "neon"),
    dox
))]
pub use self::neon::*;

pub use crate::core_arch::acle::*;

#[cfg(test)]
use stdarch_test::assert_instr;

/// Generates the trap instruction `UDF`
#[cfg(target_arch = "arm")]
#[cfg_attr(test, assert_instr(udf))]
#[inline]
pub unsafe fn udf() -> ! {
    crate::intrinsics::abort()
}
