use core::cmp::Ordering;
use core::intrinsics;
use core::marker::PhantomData;
use core::ops::{Neg, Not, Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};

use crate::symbolic::Symbolic;

pub struct Bv<S: Size + ?Sized> {
    _dummy: u8,
    _marker: PhantomData<S>,
}

pub trait Size {
    fn make_symbolic(desc: &'static str) -> Bv<Self>;
}

pub struct _128;
impl Size for _128 {
    fn make_symbolic(desc: &'static str) -> Bv<Self> { make_symbolic_128(desc) }
}

pub struct _256;
impl Size for _256 {
    fn make_symbolic(desc: &'static str) -> Bv<Self> { make_symbolic_256(desc) }
}

pub struct _512;
impl Size for _512 {
    fn make_symbolic(desc: &'static str) -> Bv<Self> { make_symbolic_512(desc) }
}


pub type Bv128 = Bv<_128>;
pub type Bv256 = Bv<_256>;
pub type Bv512 = Bv<_512>;


impl<S: Size> Bv<S> {
    pub const ZERO: Self = Bv { _dummy: 0, _marker: PhantomData };
    pub const ONE: Self = Bv { _dummy: 1, _marker: PhantomData };
    pub const MAX: Self = Bv { _dummy: 2, _marker: PhantomData };
}


/// Arbitrary bitvector-to-bitvector conversion.  Either truncates or zero-extends depending on the
/// relative sizes of `T` and `U`.  Both `T` and `U` must be represented as  bitvectors (`BVType`)
/// at the Crucible level.
pub fn convert<T, U>(x: T) -> U {
    unimplemented!()
}

macro_rules! impl_from_bv {
    ($($S1:ty, $S2:ty;)*) => {
        $(
            impl From<Bv<$S1>> for Bv<$S2> {
                fn from(x: Bv<$S1>) -> Bv<$S2> {
                    convert(x)
                }
            }
        )*
    };
}

impl_from_bv! {
    _128, _256;
    _128, _512;
    _256, _128;
    _256, _512;
    _512, _128;
    _512, _256;
}

macro_rules! impl_into_prim {
    ($($T:ty),*) => {
        $(
            impl<S: Size> From<Bv<S>> for $T {
                fn from(x: Bv<S>) -> $T {
                    convert(x)
                }
            }
        )*
    };
}

macro_rules! impl_from_into_prim {
    ($($T:ty),*) => {
        $(
            impl<S: Size> From<$T> for Bv<S> {
                fn from(x: $T) -> Bv<S> {
                    convert(x)
                }
            }
        )*
        impl_into_prim!($($T),*);
    };
}

macro_rules! impl_from_into_prim_signed {
    ($($T:ty),*) => {
        $(
            impl<S: Size> From<$T> for Bv<S> {
                fn from(x: $T) -> Bv<S> {
                    assert!(x >= 0, "can't convert negative integer to unsigned bitvector");
                    convert(x)
                }
            }
        )*
        impl_into_prim!($($T),*);
    };
}

impl_from_into_prim!(u8, u16, u32, u64, u128, usize);
impl_from_into_prim_signed!(i8, i16, i32, i64, i128, isize);


macro_rules! impl_unops {
    ($($Op:ident, $op:ident;)*) => {
        $(
            impl<S: Size> $Op for Bv<S> {
                type Output = Bv<S>;
                fn $op(self) -> Bv<S> {
                    unimplemented!()
                }
            }
        )*
    };
}

macro_rules! impl_binops {
    ($($Op:ident, $op:ident;)*) => {
        $(
            impl<S: Size> $Op<Bv<S>> for Bv<S> {
                type Output = Bv<S>;
                fn $op(self, other: Bv<S>) -> Bv<S> {
                    unimplemented!()
                }
            }
        )*
    };
}

macro_rules! impl_shift_ops {
    ($($Op:ident, $op:ident;)*) => {
        $(
            // Crucible shift ops require the shift amount and value use the same bitvector width,
            // so we convert `usize` to the right `Bv` type before calling the real shift function.

            fn $op<S: Size>(x: Bv<S>, y: Bv<S>) -> Bv<S> {
                unimplemented!()
            }

            impl<S: Size> $Op<usize> for Bv<S> {
                type Output = Bv<S>;
                fn $op(self, shift: usize) -> Bv<S> {
                    $op(self, shift.into())
                }
            }
        )*
    };
}

impl_unops! {
    Not, not;
}

impl_binops! {
    Add, add;
    Sub, sub;
    Mul, mul;
    Div, div;
    Rem, rem;
    BitAnd, bitand;
    BitOr, bitor;
    BitXor, bitxor;
}

impl_shift_ops! {
    Shl, shl;
    Shr, shr;
}


impl<S: Size> Bv<S> {
    pub fn overflowing_add(self, other: Bv<S>) -> (Bv<S>, bool) {
        unimplemented!()
    }

    pub fn overflowing_sub(self, other: Bv<S>) -> (Bv<S>, bool) {
        unimplemented!()
    }

    pub fn overflowing_mul(self, other: Bv<S>) -> (Bv<S>, bool) {
        unimplemented!()
    }

    pub fn leading_zeros(self) -> u32 {
        unimplemented!()
    }
}


impl<S: Size> Clone for Bv<S> {
    fn clone(&self) -> Bv<S> {
        *self
    }
}

impl<S: Size> Copy for Bv<S> {}

impl<S: Size> PartialEq<Bv<S>> for Bv<S> {
    fn eq(&self, other: &Bv<S>) -> bool {
        unimplemented!()
    }
}

impl<S: Size> Eq for Bv<S> {}

impl<S: Size> PartialOrd<Bv<S>> for Bv<S> {
    fn partial_cmp(&self, other: &Bv<S>) -> Option<Ordering> {
        Some(self.cmp(other))
    }

    fn lt(&self, other: &Bv<S>) -> bool {
        unimplemented!()
    }
}

impl<S: Size> Ord for Bv<S> {
    fn cmp(&self, other: &Bv<S>) -> Ordering {
        if self.eq(other) { Ordering::Equal }
        else if self.lt(other) { Ordering::Less }
        else { Ordering::Greater }
    }
}

impl<S: Size> Symbolic for Bv<S> {
    fn symbolic(desc: &'static str) -> Bv<S> {
        S::make_symbolic(desc)
    }
}

fn make_symbolic_128(desc: &'static str) -> Bv<_128> { unimplemented!() }
fn make_symbolic_256(desc: &'static str) -> Bv<_256> { unimplemented!() }
fn make_symbolic_512(desc: &'static str) -> Bv<_512> { unimplemented!() }
