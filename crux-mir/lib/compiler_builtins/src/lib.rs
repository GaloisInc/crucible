#![cfg_attr(feature = "compiler-builtins", compiler_builtins)]
#![feature(abi_unadjusted)]
#![feature(asm)]
#![feature(global_asm)]
#![feature(cfg_target_has_atomic)]
#![feature(compiler_builtins)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![feature(linkage)]
#![feature(naked_functions)]
#![feature(repr_simd)]
#![no_builtins]
#![no_std]
#![allow(unused_features)]
// We use `u128` in a whole bunch of places which we currently agree with the
// compiler on ABIs and such, so we should be "good enough" for now and changes
// to the `u128` ABI will be reflected here.
#![allow(improper_ctypes)]

// We disable #[no_mangle] for tests so that we can verify the test results
// against the native compiler-rt implementations of the builtins.

// NOTE cfg(all(feature = "c", ..)) indicate that compiler-rt provides an arch optimized
// implementation of that intrinsic and we'll prefer to use that

// NOTE(aapcs, aeabi, arm) ARM targets use intrinsics named __aeabi_* instead of the intrinsics
// that follow "x86 naming convention" (e.g. addsf3). Those aeabi intrinsics must adhere to the
// AAPCS calling convention (`extern "aapcs"`) because that's how LLVM will call them.

#[cfg(test)]
extern crate core;

fn abort() -> ! {
    unsafe { core::intrinsics::abort() }
}

#[macro_use]
mod macros;

pub mod float;
pub mod int;

#[cfg(any(
    all(target_arch = "wasm32", target_os = "unknown"),
    all(target_arch = "arm", target_os = "none"),
    all(target_vendor = "fortanix", target_env = "sgx")
))]
pub mod math;
pub mod mem;

#[cfg(target_arch = "arm")]
pub mod arm;

#[cfg(all(kernel_user_helpers, target_os = "linux", target_arch = "arm"))]
pub mod arm_linux;

#[cfg(any(target_arch = "riscv32"))]
pub mod riscv32;

#[cfg(target_arch = "x86")]
pub mod x86;

#[cfg(target_arch = "x86_64")]
pub mod x86_64;

pub mod probestack;
