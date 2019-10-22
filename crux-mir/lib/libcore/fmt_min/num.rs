//! Integer and floating-point number formatting


use crate::fmt::{self, dummy};
use crate::ops::{Div, Rem, Sub};
use crate::str;
use crate::slice;
use crate::ptr;
use crate::mem::MaybeUninit;

macro_rules! int_base {
    ($Trait:ident for $T:ident as $U:ident -> $Radix:ident) => {
        #[stable(feature = "rust1", since = "1.0.0")]
        impl fmt::$Trait for $T {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                dummy()
            }
        }
    }
}

macro_rules! debug {
    ($T:ident) => {
        #[stable(feature = "rust1", since = "1.0.0")]
        impl fmt::Debug for $T {
            #[inline]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                dummy()
            }
        }
    }
}

macro_rules! integer {
    ($Int:ident, $Uint:ident) => {
        int_base! { Binary   for $Int as $Uint  -> Binary }
        int_base! { Octal    for $Int as $Uint  -> Octal }
        int_base! { LowerHex for $Int as $Uint  -> LowerHex }
        int_base! { UpperHex for $Int as $Uint  -> UpperHex }
        debug! { $Int }

        int_base! { Binary   for $Uint as $Uint -> Binary }
        int_base! { Octal    for $Uint as $Uint -> Octal }
        int_base! { LowerHex for $Uint as $Uint -> LowerHex }
        int_base! { UpperHex for $Uint as $Uint -> UpperHex }
        debug! { $Uint }
    }
}
integer! { isize, usize }
integer! { i8, u8 }
integer! { i16, u16 }
integer! { i32, u32 }
integer! { i64, u64 }
integer! { i128, u128 }


macro_rules! impl_Display {
    ($($t:ident),* as $u:ident via $conv_fn:ident named $name:ident) => {
        fn $name(mut n: $u, is_nonnegative: bool, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            dummy()
        }

        $(
            #[stable(feature = "rust1", since = "1.0.0")]
            impl fmt::Display for $t {
                #[allow(unused_comparisons)]
                fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                    dummy()
                }
            })*
    };
}

// Include wasm32 in here since it doesn't reflect the native pointer size, and
// often cares strongly about getting a smaller code size.
#[cfg(any(target_pointer_width = "64", target_arch = "wasm32"))]
mod imp {
    use super::*;
    impl_Display!(
        i8, u8, i16, u16, i32, u32, i64, u64, usize, isize
            as u64 via to_u64 named fmt_u64
    );
}

#[cfg(not(any(target_pointer_width = "64", target_arch = "wasm32")))]
mod imp {
    use super::*;
    impl_Display!(i8, u8, i16, u16, i32, u32, isize, usize as u32 via to_u32 named fmt_u32);
    impl_Display!(i64, u64 as u64 via to_u64 named fmt_u64);
}

impl_Display!(i128, u128 as u128 via to_u128 named fmt_u128);
