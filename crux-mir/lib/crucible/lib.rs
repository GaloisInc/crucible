#![no_std]
#![feature(core_intrinsics)]
#![feature(crucible_intrinsics)]
#![feature(unboxed_closures)]
#![feature(tuple_trait)]

pub mod bitvector;
pub mod cryptol;
pub mod method_spec;
pub mod sym_bytes;
pub mod symbolic;

// These modules expose Crucible primitives for use within our custom version of `libstd`.  They
// aren't meant to be used from normal symbolic tests.
#[doc(hidden)] pub mod alloc;
#[doc(hidden)] pub use core::crucible::any;
#[doc(hidden)] pub mod array;
#[doc(hidden)] pub use core::crucible::ptr;
#[doc(hidden)] pub mod vector;

// Re-export the `Symbolic` trait, which is used to create symbolic values.
pub use self::symbolic::Symbolic;

/// Assert that a condition holds.  During symbolic testing, `crux-mir` will search for an
/// assignment to the symbolic variables that violates an assertion.
///
/// This macro works just like the standard `assert!`, but currently produces better error
/// messages.
///
/// If the error message uses string formatting, `crux-mir` will choose an arbitrary concrete
/// counterexample and use its values when formatting the message.  For example,
/// `crucible_assert!(x + y == z, "bad arithmetic: {} + {} != {}", x, y, z);` might print a message
/// like `bad arithmetic: 1 + 2 != 4`, assuming `x`, `y`, and `z` are symbolic variables that can
/// take on the values 1, 2, and 4..
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

/// Internal implementation detail of `crucible_assert!`.  Users should not call this directly -
/// use the `crucible_assert!` macro instead.
#[doc(hidden)]
pub fn crucible_assert_impl(
    _cond: bool,
    _cond_str: &str,
    _file: &'static str,
    _line: u32,
    _col: u32,
) -> () {
    ()
}

/// Assume that a condition holds.  `crux-mir` will not consider assignments to the symbolic
/// variables that violate an assumption.
#[macro_export]
macro_rules! crucible_assume {
    ($e:expr) => {
        $crate::crucible_assume_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

/// Internal implementation detail of `crucible_assume!`.  Users should not call this directly -
/// use the `crucible_assume!` macro instead.
#[doc(hidden)]
pub fn crucible_assume_impl(
    _cond: bool,
    _cond_str: &'static str,
    _file: &'static str,
    _line: u32,
    _col: u32,
) -> () {
    ()
}


/// Assert that the current code is unreachable.  This is similar to the standard `unreachable!()`
/// macro, but uses `crucible_assert!` internally.
#[macro_export]
macro_rules! crucible_assert_unreachable {
    () => {{
        $crate::crucible_assert!(false);
        unreachable!()
    }};
}

/// Assume that the current code is unreachable.  This is similar to `crucible_assume!(false)`, but
/// also returns `!`, so it can be used in positions where a return value is expected.
#[macro_export]
macro_rules! crucible_assume_unreachable {
    () => {{
        $crate::crucible_assume!(false);
        unreachable!()
    }};
}


/// Given a symbolic value, choose an arbitrary instance that satisfies the current path condition.
/// This function operates recursively: a call to `concretize(&(x, y))` (where `x` and `y` are
/// symbolic integers) will produce a concrete result like `&(1, 2)`.
///
/// This function is highly magical, and should only be used if you understand its override
/// implementation (`concretize` in `Mir/Overrides.hs`).  It's mainly intended for use in printing
/// counterexamples, where the current execution path is terminated shortly after the
/// `concretize()` call.  It's probably unwise to use this on paths that will later be joined with
/// others.
pub fn concretize<T>(x: T) -> T {
    x
}

/// Install `g` as an override for `f`.
pub fn override_<F, G>(f: F, g: G) {
    unimplemented!("crucible::override_");
}

/// Print a what4 expression to stderr.  `T` must have a primitive/base type for its Crucible
/// representation.
pub fn dump_what4<T>(desc: &str, x: T) {
}

// Some older test cases still use these functions.
#[deprecated(note = "call i8::symbolic instead")]
pub fn crucible_i8(name: &'static str) -> i8 { Symbolic::symbolic(name) }
#[deprecated(note = "call i16::symbolic instead")]
pub fn crucible_i16(name: &'static str) -> i16 { Symbolic::symbolic(name) }
#[deprecated(note = "call i32::symbolic instead")]
pub fn crucible_i32(name: &'static str) -> i32 { Symbolic::symbolic(name) }
#[deprecated(note = "call i64::symbolic instead")]
pub fn crucible_i64(name: &'static str) -> i64 { Symbolic::symbolic(name) }
#[deprecated(note = "call u8::symbolic instead")]
pub fn crucible_u8(name: &'static str) -> u8 { Symbolic::symbolic(name) }
#[deprecated(note = "call u16::symbolic instead")]
pub fn crucible_u16(name: &'static str) -> u16 { Symbolic::symbolic(name) }
#[deprecated(note = "call u32::symbolic instead")]
pub fn crucible_u32(name: &'static str) -> u32 { Symbolic::symbolic(name) }
#[deprecated(note = "call u64::symbolic instead")]
pub fn crucible_u64(name: &'static str) -> u64 { Symbolic::symbolic(name) }

/// This function is overridden and used in a few test cases that check override functionality.
#[doc(hidden)]
pub fn one() -> u8 { unimplemented!() }
