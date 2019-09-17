#![no_std]

pub mod vector;

pub fn one() -> u8 { unimplemented!() }

pub fn crucible_i8(_name: &'static str) -> i8 { unimplemented!() }
pub fn crucible_i16(_name: &'static str) -> i16 { unimplemented!() }
pub fn crucible_i32(_name: &'static str) -> i32 { unimplemented!() }
pub fn crucible_i64(_name: &'static str) -> i64 { unimplemented!() }
pub fn crucible_u8(_name: &'static str) -> u8 { unimplemented!() }
pub fn crucible_u16(_name: &'static str) -> u16 { unimplemented!() }
pub fn crucible_u32(_name: &'static str) -> u32 { unimplemented!() }
pub fn crucible_u64(_name: &'static str) -> u64 { unimplemented!() }

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
    () => {
        crucible_assume!(false);
        unreachable!();
    };
}

#[macro_export]
macro_rules! crucible_assert_unreachable {
    () => {
        crucible_assert!(false);
        unreachable!();
    };
}
