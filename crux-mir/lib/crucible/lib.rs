#![no_std]
#![feature(core_intrinsics)]
#![feature(crucible_intrinsics)]

pub mod alloc;
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
    _cond_str: &str,
    _file: &'static str,
    _line: u32,
    _col: u32,
) -> () {
    ()
}

#[macro_export]
macro_rules! crucible_assert {
    ($cond:expr) => {
        $crate::crucible_assert!($cond, stringify!($cond))
    };
    ($cond:expr, $fmt:expr) => {
        $crate::crucible_assert_impl($cond, $fmt, file!(), line!(), column!());
    };
    ($cond:expr, $fmt:expr, $($args:tt)*) => {
        if !$cond {
            $crate::crucible_assert_impl(
                false,
                // Can't use `let` here because `format_args` takes the address of temporaries.
                &format!("{}", $crate::concretize(format_args!($fmt, $($args)*))),
                file!(),
                line!(),
                column!(),
            );
        }
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


/// Make a symbolic value concrete.
///
/// This is intended for use in printing counterexamples, where the current execution path is
/// terminated shortly after the `concretize()` call.  It's probably unwise to use this on paths
/// that will later be joined with others.
pub fn concretize<T>(x: T) -> T {
    x
}
