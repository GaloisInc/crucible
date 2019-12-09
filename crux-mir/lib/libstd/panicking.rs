//! Implementation of various bits and pieces of the `panic!` macro and
//! associated runtime pieces.
//!
//! Specifically, this module contains the implementation of:
//!
//! * Panic hooks
//! * Executing a panic up to doing the actual implementation
//! * Shims around "try"

use core::panic::{BoxMeUp, PanicInfo, Location};
use crucible::crucible_assert_unreachable;

use crate::any::Any;
use crate::fmt;
use crate::intrinsics;
use crate::mem;
use crate::ptr;
use crate::raw;
use crate::sys::stdio::panic_output;
use crate::sys_common::rwlock::RWLock;
use crate::sys_common::thread_info;
use crate::sys_common::util;
use crate::thread;

/// Registers a custom panic hook, replacing any that was previously registered.
#[stable(feature = "panic_hooks", since = "1.10.0")]
pub fn set_hook(_hook: Box<dyn Fn(&PanicInfo<'_>) + 'static + Sync + Send>) {
    unimplemented!()
}

/// Unregisters the current panic hook, returning it.
#[stable(feature = "panic_hooks", since = "1.10.0")]
pub fn take_hook() -> Box<dyn Fn(&PanicInfo<'_>) + 'static + Sync + Send> {
    unimplemented!()
}


#[cfg(not(test))]
#[doc(hidden)]
#[unstable(feature = "update_panic_count", issue = "0")]
pub fn update_panic_count(_amt: isize) -> usize {
    0
}

/// Invoke a closure, capturing the cause of an unwinding panic if one occurs.
pub unsafe fn r#try<R, F: FnOnce() -> R>(_f: F) -> Result<R, Box<dyn Any + Send>> {
    unimplemented!()
}

/// Determines whether the current thread is unwinding because of panic.
pub fn panicking() -> bool {
    false
}

/// Entry point of panic from the libcore crate.
#[cfg(not(test))]
#[panic_handler]
#[unwind(allowed)]
pub fn rust_begin_panic(_info: &PanicInfo<'_>) -> ! {
    crucible_assert_unreachable!();
}

/// The entry point for panicking with a formatted message.
///
/// This is designed to reduce the amount of code required at the call
/// site as much as possible (so that `panic!()` has as low an impact
/// on (e.g.) the inlining of other functions as possible), by moving
/// the actual formatting into this shared place.
#[unstable(feature = "libstd_sys_internals",
           reason = "used by the panic! macro",
           issue = "0")]
#[cold]
// If panic_immediate_abort, inline the abort call,
// otherwise avoid inlining because of it is cold path.
#[cfg_attr(not(feature="panic_immediate_abort"),inline(never))]
#[cfg_attr(    feature="panic_immediate_abort" ,inline)]
pub fn begin_panic_fmt(msg: &fmt::Arguments<'_>,
                       file_line_col: &(&'static str, u32, u32)) -> ! {
    crucible_assert_unreachable!();
}

/// This is the entry point of panicking for panic!() and assert!().
#[unstable(feature = "libstd_sys_internals",
           reason = "used by the panic! macro",
           issue = "0")]
#[cfg_attr(not(test), lang = "begin_panic")]
// never inline unless panic_immediate_abort to avoid code
// bloat at the call sites as much as possible
#[cfg_attr(not(feature="panic_immediate_abort"),inline(never))]
#[cold]
pub fn begin_panic<M: Any + Send>(msg: M, file_line_col: &(&'static str, u32, u32)) -> ! {
    crucible_assert_unreachable!();
}

/// Shim around rust_panic. Called by resume_unwind.
pub fn update_count_then_panic(_msg: Box<dyn Any + Send>) -> ! {
    crucible_assert_unreachable!();
}
