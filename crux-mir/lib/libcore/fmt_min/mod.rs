//! Stripped-down version of `core::fmt`.  This provides all the same public definitions, but all
//! the function implementations are replaced by no-ops.
#![stable(feature = "rust1", since = "1.0.0")]

use crate::cell::{UnsafeCell, Cell, RefCell, Ref, RefMut};
use crate::marker::PhantomData;
use crate::mem;
#[cfg(flt2dec)] use crate::num::flt2dec;
use crate::ops::Deref;
use crate::result;
use crate::slice;
use crate::str;

mod float;
mod num;
mod builders;

/// Every function in this module returns a dummy value, but wraps it in a call to this `dummy_val`
/// function first.  If you want to make functions panic instead of being a no-op, change the
/// implementation here.
fn dummy_val<T>(x: T) -> T {
    x
}

/// Specialized version of `dummy_val` for the many functions that return `fmt::Result`.
fn dummy() -> Result {
    dummy_val(Ok(()))
}

#[stable(feature = "fmt_flags_align", since = "1.28.0")]
#[derive(Debug)]
pub enum Alignment {
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    Left,
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    Right,
    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    Center,
}

#[stable(feature = "debug_builders", since = "1.2.0")]
pub use self::builders::{DebugStruct, DebugTuple, DebugSet, DebugList, DebugMap};

#[unstable(feature = "fmt_internals", reason = "internal to format_args!",
           issue = "0")]
#[doc(hidden)]
pub mod rt {
    pub mod v1;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub type Result = result::Result<(), Error>;

#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct Error;

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Write {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn write_str(&mut self, s: &str) -> Result;

    #[stable(feature = "fmt_write_char", since = "1.1.0")]
    fn write_char(&mut self, c: char) -> Result {
        dummy()
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    fn write_fmt(mut self: &mut Self, args: Arguments<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "fmt_write_blanket_impl", since = "1.4.0")]
impl<W: Write + ?Sized> Write for &mut W {
    fn write_str(&mut self, s: &str) -> Result {
        (**self).write_str(s)
    }

    fn write_char(&mut self, c: char) -> Result {
        (**self).write_char(c)
    }

    fn write_fmt(&mut self, args: Arguments<'_>) -> Result {
        (**self).write_fmt(args)
    }
}

#[allow(missing_debug_implementations)]
#[stable(feature = "rust1", since = "1.0.0")]
pub struct Formatter<'a> {
    _marker: PhantomData<&'a mut (dyn Write+'a)>,
}

#[derive(Copy, Clone)]
#[allow(missing_debug_implementations)]
#[unstable(feature = "fmt_internals", reason = "internal to format_args!",
           issue = "0")]
#[doc(hidden)]
pub struct ArgumentV1<'a> {
    _marker: PhantomData<&'a (dyn Debug+'a)>,
}

impl<'a> ArgumentV1<'a> {
    #[doc(hidden)]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new<'b, T>(x: &'b T,
                      f: fn(&T, &mut Formatter<'_>) -> Result) -> ArgumentV1<'b> {
        ArgumentV1 {
            _marker: PhantomData,
        }
    }

    #[doc(hidden)]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn from_usize(x: &usize) -> ArgumentV1<'_> {
        ArgumentV1 {
            _marker: PhantomData,
        }
    }
}

impl<'a> Arguments<'a> {
    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new_v1(pieces: &'a [&'a str],
                  args: &'a [ArgumentV1<'a>]) -> Arguments<'a> {
        Arguments {
            pieces,
            fmt: None,
            args,
        }
    }

    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn new_v1_formatted(pieces: &'a [&'a str],
                            args: &'a [ArgumentV1<'a>],
                            fmt: &'a [rt::v1::Argument]) -> Arguments<'a> {
        Arguments {
            pieces,
            fmt: Some(fmt),
            args,
        }
    }

    #[doc(hidden)] #[inline]
    #[unstable(feature = "fmt_internals", reason = "internal to format_args!",
               issue = "0")]
    pub fn estimated_capacity(&self) -> usize {
        dummy_val(0)
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[derive(Copy, Clone)]
pub struct Arguments<'a> {
    // Format string pieces to print.
    pieces: &'a [&'a str],

    // Placeholder specs, or `None` if all specs are default (as in "{}{}").
    fmt: Option<&'a [rt::v1::Argument]>,

    // Dynamic arguments for interpolation, to be interleaved with string
    // pieces. (Every argument is preceded by a string piece.)
    args: &'a [ArgumentV1<'a>],
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Debug for Arguments<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Display for Arguments<'_> {
    fn fmt(&self, fmt: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
#[rustc_on_unimplemented(
    on(crate_local, label="`{Self}` cannot be formatted using `{{:?}}`",
                    note="add `#[derive(Debug)]` or manually implement `{Debug}`"),
    message="`{Self}` doesn't implement `{Debug}`",
    label="`{Self}` cannot be formatted using `{{:?}}` because it doesn't implement `{Debug}`",
)]
#[doc(alias = "{:?}")]
#[lang = "debug_trait"]
pub trait Debug {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[rustc_on_unimplemented(
    on(
        _Self="std::path::Path",
        label="`{Self}` cannot be formatted with the default formatter; call `.display()` on it",
        note="call `.display()` or `.to_string_lossy()` to safely print paths, \
              as they may contain non-Unicode data"
    ),
    message="`{Self}` doesn't implement `{Display}`",
    label="`{Self}` cannot be formatted with the default formatter",
    note="in format strings you may be able to use `{{:?}}` (or {{:#?}} for pretty-print) instead",
)]
#[doc(alias = "{}")]
#[stable(feature = "rust1", since = "1.0.0")]
pub trait Display {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Octal {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Binary {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait LowerHex {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait UpperHex {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait Pointer {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait LowerExp {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub trait UpperExp {
    #[stable(feature = "rust1", since = "1.0.0")]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result;
}

#[stable(feature = "rust1", since = "1.0.0")]
pub fn write(output: &mut dyn Write, args: Arguments<'_>) -> Result {
    dummy()
}

impl<'a> Formatter<'a> {
    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pad_integral(&mut self,
                        is_nonnegative: bool,
                        prefix: &str,
                        buf: &str)
                        -> Result {
        dummy()
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn pad(&mut self, s: &str) -> Result {
        dummy()
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn write_str(&mut self, data: &str) -> Result {
        dummy()
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    pub fn write_fmt(&mut self, fmt: Arguments<'_>) -> Result {
        dummy()
    }

    #[stable(feature = "rust1", since = "1.0.0")]
    #[rustc_deprecated(since = "1.24.0",
                       reason = "use the `sign_plus`, `sign_minus`, `alternate`, \
                                 or `sign_aware_zero_pad` methods instead")]
    pub fn flags(&self) -> u32 { dummy_val(0) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn fill(&self) -> char { dummy_val(' ') }

    #[stable(feature = "fmt_flags_align", since = "1.28.0")]
    pub fn align(&self) -> Option<Alignment> { dummy_val(None) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn width(&self) -> Option<usize> { dummy_val(None) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn precision(&self) -> Option<usize> { dummy_val(None) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_plus(&self) -> bool { dummy_val(false) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_minus(&self) -> bool { dummy_val(false) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn alternate(&self) -> bool { dummy_val(false) }

    #[stable(feature = "fmt_flags", since = "1.5.0")]
    pub fn sign_aware_zero_pad(&self) -> bool { dummy_val(false) }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn debug_struct<'b>(&'b mut self, name: &str) -> DebugStruct<'b, 'a> {
        builders::debug_struct_new(self, name)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn debug_tuple<'b>(&'b mut self, name: &str) -> DebugTuple<'b, 'a> {
        builders::debug_tuple_new(self, name)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn debug_list<'b>(&'b mut self) -> DebugList<'b, 'a> {
        builders::debug_list_new(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn debug_set<'b>(&'b mut self) -> DebugSet<'b, 'a> {
        builders::debug_set_new(self)
    }

    #[stable(feature = "debug_builders", since = "1.2.0")]
    pub fn debug_map<'b>(&'b mut self) -> DebugMap<'b, 'a> {
        builders::debug_map_new(self)
    }
}

#[stable(since = "1.2.0", feature = "formatter_write")]
impl Write for Formatter<'_> {
    fn write_str(&mut self, s: &str) -> Result {
        dummy()
    }

    fn write_char(&mut self, c: char) -> Result {
        dummy()
    }

    fn write_fmt(&mut self, args: Arguments<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Display for Error {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

// Implementations of the core formatting traits

macro_rules! fmt_refs {
    ($($tr:ident),*) => {
        $(
        #[stable(feature = "rust1", since = "1.0.0")]
        impl<T: ?Sized + $tr> $tr for &T {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result { dummy() }
        }
        #[stable(feature = "rust1", since = "1.0.0")]
        impl<T: ?Sized + $tr> $tr for &mut T {
            fn fmt(&self, f: &mut Formatter<'_>) -> Result { dummy() }
        }
        )*
    }
}

fmt_refs! { Debug, Display, Octal, Binary, LowerHex, UpperHex, LowerExp, UpperExp }

#[unstable(feature = "never_type", issue = "35121")]
impl Debug for ! {
    fn fmt(&self, _: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[unstable(feature = "never_type", issue = "35121")]
impl Display for ! {
    fn fmt(&self, _: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Debug for bool {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Display for bool {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Debug for str {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Display for str {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Debug for char {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Display for char {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Pointer for *const T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Pointer for *mut T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Pointer for &T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Pointer for &mut T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

// Implementation of Display/Debug for various core types

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Debug for *const T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result { dummy() }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Debug for *mut T {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result { dummy() }
}

macro_rules! peel {
    ($name:ident, $($other:ident,)*) => (tuple! { $($other,)* })
}

macro_rules! tuple {
    () => ();
    ( $($name:ident,)+ ) => (
        #[stable(feature = "rust1", since = "1.0.0")]
        impl<$($name:Debug),+> Debug for ($($name,)+) where last_type!($($name,)+): ?Sized {
            #[allow(non_snake_case, unused_assignments)]
            fn fmt(&self, f: &mut Formatter<'_>) -> Result {
                dummy()
            }
        }
        peel! { $($name,)+ }
    )
}

macro_rules! last_type {
    ($a:ident,) => { $a };
    ($a:ident, $($rest_a:ident,)+) => { last_type!($($rest_a,)+) };
}

tuple! { T0, T1, T2, T3, T4, T5, T6, T7, T8, T9, T10, T11, }

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Debug> Debug for [T] {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl Debug for () {
    #[inline]
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}
#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized> Debug for PhantomData<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: Copy + Debug> Debug for Cell<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Debug> Debug for RefCell<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Debug> Debug for Ref<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "rust1", since = "1.0.0")]
impl<T: ?Sized + Debug> Debug for RefMut<'_, T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

#[stable(feature = "core_impl_debug", since = "1.9.0")]
impl<T: ?Sized + Debug> Debug for UnsafeCell<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        dummy()
    }
}

// If you expected tests to be here, look instead at the ui/ifmt.rs test,
// it's a lot easier than creating all of the rt::Piece structures here.
