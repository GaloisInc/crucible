#![no_std]
#![feature(core_intrinsics)]
#![feature(crucible_intrinsics)]

pub use core::crucible::any;
pub mod array;
pub mod bitvector;
pub mod symbolic;
pub mod sym_bytes;
pub mod vector;

pub use self::symbolic::Symbolic;

pub fn one() -> u8 { unimplemented!() }

pub fn crucible_i8(name: &'static str) -> i8 { Symbolic::symbolic(name) }
pub fn crucible_i16(name: &'static str) -> i16 { Symbolic::symbolic(name) }
pub fn crucible_i32(name: &'static str) -> i32 { Symbolic::symbolic(name) }
pub fn crucible_i64(name: &'static str) -> i64 { Symbolic::symbolic(name) }
pub fn crucible_u8(name: &'static str) -> u8 { Symbolic::symbolic(name) }
pub fn crucible_u16(name: &'static str) -> u16 { Symbolic::symbolic(name) }
pub fn crucible_u32(name: &'static str) -> u32 { Symbolic::symbolic(name) }
pub fn crucible_u64(name: &'static str) -> u64 { Symbolic::symbolic(name) }

pub fn crucible_assert_impl(
    _cond: bool,
    _cond_str: &'static str,
    _file: &'static str,
    _line: u32,
    _col: u32,
) -> () {
    ()
}

#[macro_export]
macro_rules! crucible_assert {
    ($e:expr) => {
        $crate::crucible_assert_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

pub fn crucible_assume_impl(
    _cond: bool,
    _cond_str: &'static str,
    _file: &'static str,
    _line: u32,
    _col: u32,
) -> () {
    ()
}

#[macro_export]
macro_rules! crucible_assume {
    ($e:expr) => {
        $crate::crucible_assume_impl($e, stringify!($e), file!(), line!(), column!())
    };
}


#[macro_export]
macro_rules! crucible_assume_unreachable {
    () => {{
        $crate::crucible_assume!(false);
        unreachable!()
    }};
}

#[macro_export]
macro_rules! crucible_assert_unreachable {
    () => {{
        $crate::crucible_assert!(false);
        unreachable!()
    }};
}
