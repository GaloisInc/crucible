#![crate_name = "std"]
#![feature(
    core_intrinsics,
    core_panic_info,
    dropck_eyepatch,
    fundamental,
    lang_items,
    ptr_internals,
    receiver_trait,
    todo_macro,
)]
#![no_std]

extern crate crucible;

pub mod boxed;
pub mod io;
pub mod vec;

pub mod prelude {
    pub mod v1 {
        pub use core::prelude::v1::*;
        pub use crate::boxed::Box;
        pub use crate::vec::Vec;
        pub use crate::vec;
    }
}

pub use core::borrow;
pub use core::clone;
pub use core::cmp;
pub use core::convert;
pub use core::default;
pub use core::fmt;
pub use core::hash;
pub use core::intrinsics;
pub use core::iter;
pub use core::marker;
pub use core::mem;
pub use core::ops;
pub use core::option;
pub use core::ptr;
pub use core::result;
pub use core::slice;

// Macro reexports
pub use core::{assert_eq, assert_ne, debug_assert, debug_assert_eq, debug_assert_ne};
pub use core::{panic, unreachable, unimplemented, write, writeln, r#try, todo};
