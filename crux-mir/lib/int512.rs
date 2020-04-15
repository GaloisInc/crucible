#![no_std]

extern crate core;
use core::ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};
use core::cmp::{Ord, PartialOrd, Ordering};

#[derive(Copy)]
pub struct Int512 { _dummy: u8 }

pub fn clone(_i: &Int512) -> Int512 { unimplemented!() }
impl Clone for Int512 {
    fn clone(&self) -> Int512 { clone(self) }
}

pub fn symbolic(_x: &'static str) -> Int512 { unimplemented!() }
impl Int512 {
    pub fn symbolic(x: &'static str) -> Int512 { symbolic(x) }
}

macro_rules! binop {
    ($Op:ident, $op:ident) => {
        pub fn $op(_x: Int512, _y: Int512) -> Int512 { unimplemented!() }

        impl Int512 {
            pub fn $op(self, other: Int512) -> Int512 { $op(self, other) }
        }

        /*
        impl $Op<Int512> for Int512 {
            type Output = Int512;
            fn $op(self, other: Int512) -> Int512 { $op(self, other) }
        }
        */
    };
}
binop!(Add, add);
binop!(Sub, sub);
binop!(Mul, mul);
binop!(Div, div);
binop!(Rem, rem);
binop!(BitAnd, bitand);
binop!(BitOr, bitor);
binop!(BitXor, bitxor);

macro_rules! shift_op {
    ($Op:ident, $op:ident) => {
        pub fn $op(_x: Int512, _bits: u32) -> Int512 { unimplemented!() }

        impl Int512 {
            pub fn $op(self, bits: u32) -> Int512 { $op(self, bits) }
        }

        /*
        impl $Op<u32> for Int512 {
            type Output = Int512;
            fn $op(self, bits: u32) -> Int512 { $op(self, bits) }
        }
        */
    };
}
shift_op!(Shl, shl);
shift_op!(Shr, shr);

pub fn eq(_x: Int512, _y: Int512) -> bool { unimplemented!() }
impl PartialEq for Int512 {
    fn eq(&self, other: &Int512) -> bool { eq(*self, *other) }
    fn ne(&self, other: &Int512) -> bool { !eq(*self, *other) }
}
impl Eq for Int512 {}

pub fn lt(_x: Int512, _y: Int512) -> bool { unimplemented!() }
impl PartialOrd for Int512 {
    fn partial_cmp(&self, other: &Int512) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Int512 {
    fn cmp(&self, other: &Int512) -> Ordering {
        if eq(*self, *other) { Ordering::Equal }
        else if lt(*self, *other) { Ordering::Less }
        else { Ordering::Greater }
    }
}

macro_rules! prim_cast {
    ($Prim:ident) => {
        pub mod $Prim {
            use super::Int512;
            pub fn from_prim(_x: $Prim) -> Int512 { unimplemented!() }
            pub fn as_prim(_x: Int512) -> $Prim { unimplemented!() }
        }

        impl From<$Prim> for Int512 {
            fn from(x: $Prim) -> Int512 { self::$Prim::from_prim(x) }
        }

        impl From<Int512> for $Prim {
            fn from(x: Int512) -> $Prim { self::$Prim::as_prim(x) }
        }
    };
}
prim_cast!(u8);
prim_cast!(u16);
prim_cast!(u32);
prim_cast!(u64);
prim_cast!(u128);
prim_cast!(usize);
prim_cast!(i8);
prim_cast!(i16);
prim_cast!(i32);
prim_cast!(i64);
prim_cast!(i128);
prim_cast!(isize);


impl From<[u8; 32]> for Int512 {
    fn from(x: [u8; 32]) -> Int512 {
        let mut acc = Int512::from(0_i32);
        for i in 0..5 {
            acc = acc.bitor(Int512::from(x[i]).shl(8 * i as u32));
        }
        acc
    }
}

impl From<Int512> for [u8; 32] {
    fn from(x: Int512) -> [u8; 32] {
        let mut acc = [0; 32];
        let mask: Int512 = Int512::from((1_u64 << 8) - 1);
        for i in 0..32 {
            acc[i] = u8::from(x.shr(8 * i as u32).bitand(mask));
        }
        acc
    }
}
