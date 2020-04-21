//! Implementation of panics via stack unwinding
//!
//! This crate is an implementation of panics in Rust using "most native" stack
//! unwinding mechanism of the platform this is being compiled for. This
//! essentially gets categorized into three buckets currently:
//!
//! 1. MSVC targets use SEH in the `seh.rs` file.
//! 2. Emscripten uses C++ exceptions in the `emcc.rs` file.
//! 3. All other targets use libunwind/libgcc in the `gcc.rs` file.
//!
//! More documentation about each implementation can be found in the respective
//! module.

#![no_std]
#![unstable(feature = "panic_unwind", issue = "32837")]
#![doc(
    html_root_url = "https://doc.rust-lang.org/nightly/",
    issue_tracker_base_url = "https://github.com/rust-lang/rust/issues/"
)]
#![feature(core_intrinsics)]
#![feature(lang_items)]
#![feature(libc)]
#![feature(nll)]
#![feature(panic_unwind)]
#![feature(staged_api)]
#![feature(std_internals)]
#![feature(unwind_attributes)]
#![feature(abi_thiscall)]
#![feature(rustc_attrs)]
#![feature(raw)]
#![panic_runtime]
#![feature(panic_runtime)]
// `real_imp` is unused with Miri, so silence warnings.
#![cfg_attr(miri, allow(dead_code))]

use alloc::boxed::Box;
use core::any::Any;
use core::panic::BoxMeUp;

cfg_if::cfg_if! {
    if #[cfg(target_os = "emscripten")] {
        #[path = "emcc.rs"]
        mod real_imp;
    } else if #[cfg(target_arch = "wasm32")] {
        #[path = "dummy.rs"]
        mod real_imp;
    } else if #[cfg(target_os = "hermit")] {
        #[path = "hermit.rs"]
        mod real_imp;
    } else if #[cfg(all(target_env = "msvc", target_arch = "aarch64"))] {
        #[path = "dummy.rs"]
        mod real_imp;
    } else if #[cfg(target_env = "msvc")] {
        #[path = "seh.rs"]
        mod real_imp;
    } else {
        // Rust runtime's startup objects depend on these symbols, so make them public.
        #[cfg(all(target_os="windows", target_arch = "x86", target_env="gnu"))]
        pub use real_imp::eh_frame_registry::*;
        #[path = "gcc.rs"]
        mod real_imp;
    }
}

cfg_if::cfg_if! {
    if #[cfg(miri)] {
        // Use the Miri runtime.
        // We still need to also load the normal runtime above, as rustc expects certain lang
        // items from there to be defined.
        #[path = "miri.rs"]
        mod imp;
    } else {
        // Use the real runtime.
        use real_imp as imp;
    }
}

extern "C" {
    /// Handler in libstd called when a panic object is dropped outside of
    /// `catch_unwind`.
    fn __rust_drop_panic() -> !;
}

mod dwarf;

#[rustc_std_internal_symbol]
pub unsafe extern "C" fn __rust_panic_cleanup(payload: *mut u8) -> *mut (dyn Any + Send + 'static) {
    Box::into_raw(imp::cleanup(payload))
}

// Entry point for raising an exception, just delegates to the platform-specific
// implementation.
#[rustc_std_internal_symbol]
#[unwind(allowed)]
pub unsafe extern "C" fn __rust_start_panic(payload: usize) -> u32 {
    let payload = payload as *mut &mut dyn BoxMeUp;
    let payload = (*payload).take_box();

    imp::panic(Box::from_raw(payload))
}
