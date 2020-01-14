// Copyright 2015-2017 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

// Code derived from original work by Andrew Poelstra <apoelstra@wpsoftware.net>

// Rust Bitcoin Library
// Written in 2014 by
//     Andrew Poelstra <apoelstra@wpsoftware.net>
//
// To the extent possible under law, the author(s) have dedicated all
// copyright and related and neighboring rights to this software to
// the public domain worldwide. This software is distributed without
// any warranty.
//
// You should have received a copy of the CC0 Public Domain Dedication
// along with this software.
// If not, see <http://creativecommons.org/publicdomain/zero/1.0/>.
//

//! Big unsigned integer types.
//!
//! Implementation of a various large-but-fixed sized unsigned integer types.
//! The functions here are designed to be fast. There are optional `x86_64`
//! implementations for even more speed, hidden behind the `x64_arithmetic`
//! feature flag.

use core::{str, mem};
use core::ops::{Shr, Shl, BitAnd, BitOr, BitXor, Not, Div, Rem, Mul, Add, Sub};

use byteorder::{ByteOrder, BigEndian, LittleEndian};

/// Conversion from decimal string error
#[derive(Debug, PartialEq)]
pub enum FromDecStrErr {
	/// Char not from range 0-9
	InvalidCharacter,
	/// Value does not fit into type
	InvalidLength,
}

macro_rules! impl_map_from {
	($thing:ident, $from:ty, $to:ty) => {
		impl From<$from> for $thing {
			fn from(value: $from) -> $thing {
				From::from(value as $to)
			}
		}
	}
}

macro_rules! uint_overflowing_add {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		uint_overflowing_add_reg!($name, $n_words, $self_expr, $other)
	})
}

macro_rules! uint_overflowing_add_reg {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		uint_overflowing_binop!(
			$name,
			$n_words,
			$self_expr,
			$other,
			u64::overflowing_add
		)
	})
}

macro_rules! uint_overflowing_sub {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		uint_overflowing_sub_reg!($name, $n_words, $self_expr, $other)
	})
}

macro_rules! uint_overflowing_binop {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr, $fn:expr) => ({
		let $name(ref me) = $self_expr;
		let $name(ref you) = $other;

		let mut ret = unsafe { ::core::mem::uninitialized() };
		let ret_ptr = &mut ret as *mut [u64; $n_words] as *mut u64;
		let mut carry = 0u64;

		unroll! {
			for i in 0..$n_words {
				use ::core::ptr;

				if carry != 0 {
					let (res1, overflow1) = ($fn)(me[i], you[i]);
					let (res2, overflow2) = ($fn)(res1, carry);

					unsafe {
						ptr::write(
							ret_ptr.offset(i as _),
							res2
						);
					}
					carry = (overflow1 as u8 + overflow2 as u8) as u64;
				} else {
					let (res, overflow) = ($fn)(me[i], you[i]);

					unsafe {
						ptr::write(
							ret_ptr.offset(i as _),
							res
						);
					}

					carry = overflow as u64;
				}
			}
		}

		($name(ret), carry > 0)
	})
}

macro_rules! uint_overflowing_sub_reg {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		uint_overflowing_binop!(
			$name,
			$n_words,
			$self_expr,
			$other,
			u64::overflowing_sub
		)
	})
}

macro_rules! uint_overflowing_mul {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		uint_overflowing_mul_reg!($name, $n_words, $self_expr, $other)
	})
}

macro_rules! uint_full_mul_reg {
	($name:ident, 8, $self_expr:expr, $other:expr) => {
		uint_full_mul_reg!($name, 8, $self_expr, $other, |a, b| a != 0 || b != 0);
	};
	($name:ident, $n_words:tt, $self_expr:expr, $other:expr) => {
		uint_full_mul_reg!($name, $n_words, $self_expr, $other, |_, _| true);
	};
	($name:ident, $n_words:tt, $self_expr:expr, $other:expr, $check:expr) => ({{
		#![allow(unused_assignments)]

		let $name(ref me) = $self_expr;
		let $name(ref you) = $other;
		let mut ret = [0u64; $n_words * 2];

		unroll! {
			for i in 0..$n_words {
				let mut carry = 0u64;
				let b = you[i];

				unroll! {
					for j in 0..$n_words {
						if $check(me[j], carry) {
							let a = me[j];

							let (hi, low) = split_u128(a as u128 * b as u128);

							let overflow = {
								let existing_low = &mut ret[i + j];
								let (low, o) = low.overflowing_add(*existing_low);
								*existing_low = low;
								o
							};

							carry = {
								let existing_hi = &mut ret[i + j + 1];
								let hi = hi + overflow as u64;
								let (hi, o0) = hi.overflowing_add(carry);
								let (hi, o1) = hi.overflowing_add(*existing_hi);
								*existing_hi = hi;

								(o0 | o1) as u64
							}
						}
					}
				}
			}
		}

		ret
	}});
}

macro_rules! uint_overflowing_mul_reg {
	($name:ident, $n_words:tt, $self_expr: expr, $other: expr) => ({
		let ret: [u64; $n_words * 2] = uint_full_mul_reg!($name, $n_words, $self_expr, $other);

		// The safety of this is enforced by the compiler
		let ret: [[u64; $n_words]; 2] = unsafe { mem::transmute(ret) };

		// The compiler WILL NOT inline this if you remove this annotation.
		#[inline(always)]
		fn any_nonzero(arr: &[u64; $n_words]) -> bool {
			unroll! {
				for i in 0..$n_words {
					if arr[i] != 0 {
						return true;
					}
				}
			}

			false
		}

		($name(ret[0]), any_nonzero(&ret[1]))
	})
}

macro_rules! overflowing {
	($op: expr, $overflow: expr) => (
		{
			let (overflow_x, overflow_overflow) = $op;
			$overflow |= overflow_overflow;
			overflow_x
		}
	);
	($op: expr) => (
		{
			let (overflow_x, _overflow_overflow) = $op;
			overflow_x
		}
	);
}

macro_rules! panic_on_overflow {
	($name: expr) => {
		if $name {
			panic!("arithmetic operation overflow")
		}
	}
}

#[inline(always)]
fn mul_u32(a: (u64, u64), b: u64, carry: u64) -> (u64, u64) {
	let upper = b * a.0;
	let lower = b * a.1;

	let (res1, overflow1) = lower.overflowing_add(upper << 32);
	let (res2, overflow2) = res1.overflowing_add(carry);

	let carry = (upper >> 32) + overflow1 as u64 + overflow2 as u64;
	(res2, carry)
}

#[inline(always)]
fn split(a: u64) -> (u64, u64) {
	(a >> 32, a & 0xFFFFFFFF)
}

#[inline(always)]
fn split_u128(a: u128) -> (u64, u64) {
	((a >> 64) as _, (a & 0xFFFFFFFFFFFFFFFF) as _)
}

macro_rules! construct_uint {
	($name:ident, $n_words:tt) => (
		/// Little-endian large integer type
		#[repr(C)]
		#[derive(Copy, Clone, Eq, PartialEq, Hash)]
		#[cfg_attr(feature="serialize", derive(Serialize, Deserialize))]
		pub struct $name(pub [u64; $n_words]);

		impl $name {
			pub const MAX: $name = $name([u64::max_value(); $n_words]);

			/// Convert from a decimal string.
			pub fn from_dec_str(value: &str) -> Result<Self, FromDecStrErr> {
				if !value.bytes().all(|b| b >= 48 && b <= 57) {
					return Err(FromDecStrErr::InvalidCharacter)
				}

				let mut res = Self::default();
				for b in value.bytes().map(|b| b - 48) {
					let (r, overflow) = res.overflowing_mul_u32(10);
					if overflow {
						return Err(FromDecStrErr::InvalidLength);
					}
					let (r, overflow) = r.overflowing_add(b.into());
					if overflow {
						return Err(FromDecStrErr::InvalidLength);
					}
					res = r;
				}
				Ok(res)
			}

			/// Conversion to u32
			#[inline]
			pub fn low_u32(&self) -> u32 {
				let &$name(ref arr) = self;
				arr[0] as u32
			}

			/// Conversion to u64
			#[inline]
			pub fn low_u64(&self) -> u64 {
				let &$name(ref arr) = self;
				arr[0]
			}

			/// Conversion to u32 with overflow checking
			///
			/// # Panics
			///
			/// Panics if the number is larger than 2^32.
			#[inline]
			pub fn as_u32(&self) -> u32 {
				let &$name(ref arr) = self;
				if (arr[0] & (0xffffffffu64 << 32)) != 0 {
					panic!("Integer overflow when casting U256")
				}
				self.as_u64() as u32
			}

			/// Conversion to u64 with overflow checking
			///
			/// # Panics
			///
			/// Panics if the number is larger than 2^64.
			#[inline]
			pub fn as_u64(&self) -> u64 {
				let &$name(ref arr) = self;
				for i in 1..$n_words {
					if arr[i] != 0 {
						panic!("Integer overflow when casting U256")
					}
				}
				arr[0]
			}

			/// Whether this is zero.
			#[inline]
			pub fn is_zero(&self) -> bool {
				let &$name(ref arr) = self;
				for i in 0..$n_words { if arr[i] != 0 { return false; } }
				return true;
			}

			/// Return the least number of bits needed to represent the number
			#[inline]
			pub fn bits(&self) -> usize {
				let &$name(ref arr) = self;
				for i in 1..$n_words {
					if arr[$n_words - i] > 0 { return (0x40 * ($n_words - i + 1)) - arr[$n_words - i].leading_zeros() as usize; }
				}
				0x40 - arr[0].leading_zeros() as usize
			}

			/// Return if specific bit is set.
			///
			/// # Panics
			///
			/// Panics if `index` exceeds the bit width of the number.
			#[inline]
			pub fn bit(&self, index: usize) -> bool {
				let &$name(ref arr) = self;
				arr[index / 64] & (1 << (index % 64)) != 0
			}

			/// Returns the number of leading zeros in the binary representation of self.
			pub fn leading_zeros(&self) -> u32 {
				let mut r = 0;
				for i in 0..$n_words {
					let w = self.0[$n_words - i - 1];
					if w == 0 {
						r += 64;
					} else {
						r += w.leading_zeros();
						break;
					}
				}
				r
			}

			/// Returns the number of leading zeros in the binary representation of self.
			pub fn trailing_zeros(&self) -> u32 {
				let mut r = 0;
				for i in 0..$n_words {
					let w = self.0[i];
					if w == 0 {
						r += 64;
					} else {
						r += w.trailing_zeros();
						break;
					}
				}
				r
			}

			/// Return specific byte.
			///
			/// # Panics
			///
			/// Panics if `index` exceeds the byte width of the number.
			#[inline]
			pub fn byte(&self, index: usize) -> u8 {
				let &$name(ref arr) = self;
				(arr[index / 8] >> (((index % 8)) * 8)) as u8
			}

			/// Write to the slice in big-endian format.
			#[inline]
			pub fn to_big_endian(&self, bytes: &mut [u8]) {
				debug_assert!($n_words * 8 == bytes.len());
				for i in 0..$n_words {
					BigEndian::write_u64(&mut bytes[8 * i..], self.0[$n_words - i - 1]);
				}
			}

			/// Write to the slice in little-endian format.
			#[inline]
			pub fn to_little_endian(&self, bytes: &mut [u8]) {
				debug_assert!($n_words * 8 == bytes.len());
				for i in 0..$n_words {
					LittleEndian::write_u64(&mut bytes[8 * i..], self.0[i]);
				}
			}

			/// Convert to hex string.
			#[cfg(feature="std")]
			#[inline]
			pub fn to_hex(&self) -> String {
				use core::cmp;
				use rustc_hex::ToHex;;

				if self.is_zero() { return "0".to_owned(); } // special case.
				let mut bytes = [0u8; 8 * $n_words];
				self.to_big_endian(&mut bytes);
				let bp7 = self.bits() + 7;
				let len = cmp::max(bp7 / 8, 1);
				let bytes_hex = bytes[bytes.len() - len..].to_hex();
				(&bytes_hex[1 - bp7 % 8 / 4..]).to_owned()
			}

			/// Create `10**n` as this type.
			///
			/// # Panics
			///
			/// Panics if the result overflows the type.
			#[inline]
			pub fn exp10(n: usize) -> Self {
				match n {
					0 => Self::from(1u64),
					_ => Self::exp10(n - 1).mul_u32(10)
				}
			}

			/// Zero (additive identity) of this type.
			#[inline]
			pub fn zero() -> Self {
				From::from(0u64)
			}

			/// One (multiplicative identity) of this type.
			#[inline]
			pub fn one() -> Self {
				From::from(1u64)
			}

			/// The maximum value which can be inhabited by this type.
			#[inline]
			pub fn max_value() -> Self {
				let mut result = [0; $n_words];
				for i in 0..$n_words {
					result[i] = u64::max_value();
				}
				$name(result)
			}

			/// Fast exponentation by squaring
			/// https://en.wikipedia.org/wiki/Exponentiation_by_squaring
			///
			/// # Panics
			///
			/// Panics if the result overflows the type.
			pub fn pow(self, expon: Self) -> Self {
				if expon.is_zero() {
					return Self::one()
				}
				let is_even = |x : &Self| x.low_u64() & 1 == 0;

				let u_one = Self::one();
				let mut y = u_one;
				let mut n = expon;
				let mut x = self;
				while n > u_one {
					if is_even(&n) {
						x = x * x;
						n = n >> 1;
					} else {
						y = x * y;
						x = x * x;
						// to reduce odd number by 1 we should just clear the last bit
						n.0[$n_words-1] = n.0[$n_words-1] & ((!0u64)>>1);
						n = n >> 1;
					}
				}
				x * y
			}

			/// Fast exponentation by squaring
			/// https://en.wikipedia.org/wiki/Exponentiation_by_squaring
			pub fn overflowing_pow(self, expon: Self) -> (Self, bool) {
				if expon.is_zero() { return (Self::one(), false) }

				let is_even = |x : &Self| x.low_u64() & 1 == 0;

				let u_one = Self::one();
				let mut y = u_one;
				let mut n = expon;
				let mut x = self;
				let mut overflow = false;

				while n > u_one {
					if is_even(&n) {
						x = overflowing!(x.overflowing_mul(x), overflow);
						n = n >> 1;
					} else {
						y = overflowing!(x.overflowing_mul(y), overflow);
						x = overflowing!(x.overflowing_mul(x), overflow);
						n = (n - u_one) >> 1;
					}
				}
				let res = overflowing!(x.overflowing_mul(y), overflow);
				(res, overflow)
			}

			/// Optimized instructions
			#[inline(always)]
			pub fn overflowing_add(self, other: $name) -> ($name, bool) {
				uint_overflowing_add!($name, $n_words, self, other)
			}

			/// Addition which saturates at the maximum value.
			pub fn saturating_add(self, other: $name) -> $name {
				match self.overflowing_add(other) {
					(_, true) => $name::max_value(),
					(val, false) => val,
				}
			}

			/// Subtraction which underflows and returns a flag if it does.
			#[inline(always)]
			pub fn overflowing_sub(self, other: $name) -> ($name, bool) {
				uint_overflowing_sub!($name, $n_words, self, other)
			}

			/// Subtraction which saturates at zero.
			pub fn saturating_sub(self, other: $name) -> $name {
				match self.overflowing_sub(other) {
					(_, true) => $name::zero(),
					(val, false) => val,
				}
			}

			/// Multiply with overflow, returning a flag if it does.
			#[inline(always)]
			pub fn overflowing_mul(self, other: $name) -> ($name, bool) {
				uint_overflowing_mul!($name, $n_words, self, other)
			}

			/// Multiplication which saturates at the maximum value..
			pub fn saturating_mul(self, other: $name) -> $name {
				match self.overflowing_mul(other) {
					(_, true) => $name::max_value(),
					(val, false) => val,
				}
			}

			/// Division with overflow
			pub fn overflowing_div(self, other: $name) -> ($name, bool) {
				(self / other, false)
			}

			/// Modulus with overflow.
			pub fn overflowing_rem(self, other: $name) -> ($name, bool) {
				(self % other, false)
			}

			/// Negation with overflow.
			pub fn overflowing_neg(self) -> ($name, bool) {
				(!self, true)
			}

			/// Multiplication by u32
			#[allow(dead_code)] // not used when multiplied with inline assembly
			fn mul_u32(self, other: u32) -> Self {
				let (ret, overflow) = self.overflowing_mul_u32(other);
				panic_on_overflow!(overflow);
				ret
			}

			/// Overflowing multiplication by u32
			#[allow(dead_code)] // not used when multiplied with inline assembly
			fn overflowing_mul_u32(self, other: u32) -> (Self, bool) {
				let $name(ref arr) = self;
				let mut ret = [0u64; $n_words];
				let mut carry = 0;
				let o = other as u64;

				for i in 0..$n_words {
					let (res, carry2) = mul_u32(split(arr[i]), o, carry);
					ret[i] = res;
					carry = carry2;
				}

				($name(ret), carry > 0)
			}

			/// Converts from big endian representation bytes in memory
			/// Can also be used as (&slice).into(), as it is default `From`
			/// slice implementation for U256
			pub fn from_big_endian(slice: &[u8]) -> Self {
				assert!($n_words * 8 >= slice.len());

				let mut ret = [0; $n_words];
				unsafe {
					let ret_u8: &mut [u8; $n_words * 8] = mem::transmute(&mut ret);
					let mut ret_ptr = ret_u8.as_mut_ptr();
					let mut slice_ptr = slice.as_ptr().offset(slice.len() as isize - 1);
					for _ in 0..slice.len() {
						*ret_ptr = *slice_ptr;
						ret_ptr = ret_ptr.offset(1);
						slice_ptr = slice_ptr.offset(-1);
					}
				}

				$name(ret)
			}

			/// Converts from little endian representation bytes in memory
			pub fn from_little_endian(slice: &[u8]) -> Self {
				assert!($n_words * 8 >= slice.len());

				let mut ret = [0; $n_words];
				unsafe {
					let ret_u8: &mut [u8; $n_words * 8] = mem::transmute(&mut ret);
					ret_u8[0..slice.len()].copy_from_slice(&slice);
				}

				$name(ret)
			}
		}

		impl Default for $name {
			fn default() -> Self {
				$name::zero()
			}
		}

		impl From<u64> for $name {
			fn from(value: u64) -> $name {
				let mut ret = [0; $n_words];
				ret[0] = value;
				$name(ret)
			}
		}


		impl_map_from!($name, u8, u64);
		impl_map_from!($name, u16, u64);
		impl_map_from!($name, u32, u64);
		impl_map_from!($name, usize, u64);

		impl From<i64> for $name {
			fn from(value: i64) -> $name {
				match value >= 0 {
					true => From::from(value as u64),
					false => { panic!("Unsigned integer can't be created from negative value"); }
				}
			}
		}

		impl_map_from!($name, i8, i64);
		impl_map_from!($name, i16, i64);
		impl_map_from!($name, i32, i64);
		impl_map_from!($name, isize, i64);

		// Converts from big endian representation of U256
		impl<'a> From<&'a [u8]> for $name {
			fn from(bytes: &[u8]) -> $name {
				Self::from_big_endian(bytes)
			}
		}

		#[cfg(feature="std")]
		impl str::FromStr for $name {
			type Err = ::rustc_hex::FromHexError;

			fn from_str(value: &str) -> Result<$name, Self::Err> {
				use rustc_hex::FromHex;

				let bytes: Vec<u8> = match value.len() % 2 == 0 {
					true => try!(value.from_hex()),
					false => try!(("0".to_owned() + value).from_hex())
				};

				let bytes_ref: &[u8] = &bytes;
				Ok(From::from(bytes_ref))
			}
		}

		impl Add<$name> for $name {
			type Output = $name;

			fn add(self, other: $name) -> $name {
				let (result, overflow) = self.overflowing_add(other);
				panic_on_overflow!(overflow);
				result
			}
		}

		impl Sub<$name> for $name {
			type Output = $name;

			#[inline]
			fn sub(self, other: $name) -> $name {
				let (result, overflow) = self.overflowing_sub(other);
				panic_on_overflow!(overflow);
				result
			}
		}

		impl Mul<$name> for $name {
			type Output = $name;

			fn mul(self, other: $name) -> $name {
				let (result, overflow) = self.overflowing_mul(other);
				panic_on_overflow!(overflow);
				result
			}
		}

		impl Div<$name> for $name {
			type Output = $name;

			fn div(self, other: $name) -> $name {
				let mut sub_copy = self;
				let mut shift_copy = other;
				let mut ret = [0u64; $n_words];

				let my_bits = self.bits();
				let your_bits = other.bits();

				// Check for division by 0
				assert!(your_bits != 0);

				// Early return in case we are dividing by a larger number than us
				if my_bits < your_bits {
					return $name(ret);
				}

				// Bitwise long division
				let mut shift = my_bits - your_bits;
				shift_copy = shift_copy << shift;
				loop {
					if sub_copy >= shift_copy {
						ret[shift / 64] |= 1 << (shift % 64);
						sub_copy = overflowing!(sub_copy.overflowing_sub(shift_copy));
					}
					shift_copy = shift_copy >> 1;
					if shift == 0 { break; }
					shift -= 1;
				}

				$name(ret)
			}
		}

		impl Rem<$name> for $name {
			type Output = $name;

			fn rem(self, other: $name) -> $name {
				let times = self / other;
				self - (times * other)
			}
		}

		impl BitAnd<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitand(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] & arr2[i];
				}
				$name(ret)
			}
		}

		impl BitXor<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitxor(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] ^ arr2[i];
				}
				$name(ret)
			}
		}

		impl BitOr<$name> for $name {
			type Output = $name;

			#[inline]
			fn bitor(self, other: $name) -> $name {
				let $name(ref arr1) = self;
				let $name(ref arr2) = other;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = arr1[i] | arr2[i];
				}
				$name(ret)
			}
		}

		impl Not for $name {
			type Output = $name;

			#[inline]
			fn not(self) -> $name {
				let $name(ref arr) = self;
				let mut ret = [0u64; $n_words];
				for i in 0..$n_words {
					ret[i] = !arr[i];
				}
				$name(ret)
			}
		}

		impl Shl<usize> for $name {
			type Output = $name;

			fn shl(self, shift: usize) -> $name {
				let $name(ref original) = self;
				let mut ret = [0u64; $n_words];
				let word_shift = shift / 64;
				let bit_shift = shift % 64;

				// shift
				for i in word_shift..$n_words {
					ret[i] = original[i - word_shift] << bit_shift;
				}
				// carry
				if bit_shift > 0 {
					for i in word_shift+1..$n_words {
						ret[i] += original[i - 1 - word_shift] >> (64 - bit_shift);
					}
				}
				$name(ret)
			}
		}

		impl Shr<usize> for $name {
			type Output = $name;

			fn shr(self, shift: usize) -> $name {
				let $name(ref original) = self;
				let mut ret = [0u64; $n_words];
				let word_shift = shift / 64;
				let bit_shift = shift % 64;

				// shift
				for i in word_shift..$n_words {
					ret[i - word_shift] = original[i] >> bit_shift;
				}

				// Carry
				if bit_shift > 0 {
					for i in word_shift+1..$n_words {
						ret[i - word_shift - 1] += original[i] << (64 - bit_shift);
					}
				}

				$name(ret)
			}
		}

		impl Ord for $name {
			fn cmp(&self, other: &$name) -> ::core::cmp::Ordering {
				let &$name(ref me) = self;
				let &$name(ref you) = other;
				let mut i = $n_words;
				while i > 0 {
					i -= 1;
					if me[i] < you[i] { return ::core::cmp::Ordering::Less; }
					if me[i] > you[i] { return ::core::cmp::Ordering::Greater; }
				}
				::core::cmp::Ordering::Equal
			}
		}

		impl PartialOrd for $name {
			fn partial_cmp(&self, other: &$name) -> Option<::core::cmp::Ordering> {
				Some(self.cmp(other))
			}
		}

		impl ::core::fmt::Debug for $name {
			fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
				::core::fmt::Display::fmt(self, f)
			}
		}

		impl ::core::fmt::Display for $name {
			fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
				if self.is_zero() {
					return write!(f, "0");
				}

				let mut buf = [0_u8; $n_words*20];
				let mut i = buf.len() - 1;
				let mut current = *self;
				let ten = $name::from(10);

				loop {
					let digit = (current % ten).low_u64() as u8;
					buf[i] = digit + b'0';
					current = current / ten;
					if current.is_zero() {
						break;
					}
					i -= 1;
				}

				// sequence of `'0'..'9'` chars is guaranteed to be a valid UTF8 string
				let s = unsafe {::core::str::from_utf8_unchecked(&buf[i..])};
				f.write_str(s)
			}
		}

		impl ::core::fmt::LowerHex for $name {
			fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
				let &$name(ref data) = self;
				try!(write!(f, "0x"));
				let mut latch = false;
				for ch in data.iter().rev() {
					for x in 0..16 {
						let nibble = (ch & (15u64 << ((15 - x) * 4) as u64)) >> (((15 - x) * 4) as u64);
						if !latch { latch = nibble != 0 }
						if latch {
							try!(write!(f, "{:x}", nibble));
						}
					}
				}
				Ok(())
			}
		}

		#[cfg(feature="std")]
		impl From<&'static str> for $name {
			fn from(s: &'static str) -> Self {
				s.parse().unwrap()
			}
		}
	);
}

construct_uint!(U128, 2);
construct_uint!(U256, 4);
construct_uint!(U512, 8);

impl U256 {
	/// Multiplies two 256-bit integers to produce full 512-bit integer
	/// No overflow possible
	#[inline(always)]
	pub fn full_mul(self, other: U256) -> U512 {
		U512(uint_full_mul_reg!(U256, 4, self, other))
	}

	/// Find modular inverse by modulo p
	pub fn mod_inverse(self, p: Self) -> Self {
		let mut mn = (p, self);
		let mut xy = (U256::zero(), U256::one());

		while mn.1 != U256::zero() {
			let sb: U256 = ((mn.0 / mn.1).full_mul(xy.1) % U512::from(p)).into();
			if sb > xy.0 {
				xy = (xy.1, p - ((sb - xy.0) % p))
			} else {
				xy = (xy.1, xy.0 - sb)
			}
			mn = (mn.1, mn.0 % mn.1);
		}

		xy.0
	}
}

impl From<U256> for U512 {
	fn from(value: U256) -> U512 {
		let U256(ref arr) = value;
		let mut ret = [0; 8];
		ret[0] = arr[0];
		ret[1] = arr[1];
		ret[2] = arr[2];
		ret[3] = arr[3];
		U512(ret)
	}
}

impl From<U512> for U256 {
	fn from(value: U512) -> U256 {
		let U512(ref arr) = value;
		if arr[4] | arr[5] | arr[6] | arr[7] != 0 {
			panic!("Overflow");
		}
		let mut ret = [0; 4];
		ret[0] = arr[0];
		ret[1] = arr[1];
		ret[2] = arr[2];
		ret[3] = arr[3];
		U256(ret)
	}
}

impl<'a> From<&'a U256> for U512 {
	fn from(value: &'a U256) -> U512 {
		let U256(ref arr) = *value;
		let mut ret = [0; 8];
		ret[0] = arr[0];
		ret[1] = arr[1];
		ret[2] = arr[2];
		ret[3] = arr[3];
		U512(ret)
	}
}

impl<'a> From<&'a U512> for U256 {
	fn from(value: &'a U512) -> U256 {
		let U512(ref arr) = *value;
		if arr[4] | arr[5] | arr[6] | arr[7] != 0 {
			panic!("Overflow");
		}
		let mut ret = [0; 4];
		ret[0] = arr[0];
		ret[1] = arr[1];
		ret[2] = arr[2];
		ret[3] = arr[3];
		U256(ret)
	}
}

impl From<U256> for U128 {
	fn from(value: U256) -> U128 {
		let U256(ref arr) = value;
		if arr[2] | arr[3] != 0 {
			panic!("Overflow");
		}
		let mut ret = [0; 2];
		ret[0] = arr[0];
		ret[1] = arr[1];
		U128(ret)
	}
}

impl From<U512> for U128 {
	fn from(value: U512) -> U128 {
		let U512(ref arr) = value;
		if arr[2] | arr[3] | arr[4] | arr[5] | arr[6] | arr[7] != 0 {
			panic!("Overflow");
		}
		let mut ret = [0; 2];
		ret[0] = arr[0];
		ret[1] = arr[1];
		U128(ret)
	}
}

impl From<U128> for U512 {
	fn from(value: U128) -> U512 {
		let U128(ref arr) = value;
		let mut ret = [0; 8];
		ret[0] = arr[0];
		ret[1] = arr[1];
		U512(ret)
	}
}

impl From<U128> for U256 {
	fn from(value: U128) -> U256 {
		let U128(ref arr) = value;
		let mut ret = [0; 4];
		ret[0] = arr[0];
		ret[1] = arr[1];
		U256(ret)
	}
}

impl From<U256> for u64 {
	fn from(value: U256) -> u64 {
		value.as_u64()
	}
}

impl From<U256> for u32 {
	fn from(value: U256) -> u32 {
		value.as_u32()
	}
}

impl<'a> From<&'a [u8; 32]> for U256 {
	fn from(bytes: &[u8; 32]) -> Self {
		bytes[..].into()
	}
}

impl From<[u8; 32]> for U256 {
	fn from(bytes: [u8; 32]) -> Self {
		bytes[..].as_ref().into()
	}
}

impl From<U256> for [u8; 32] {
	fn from(number: U256) -> Self {
		let mut arr = [0u8; 32];
		number.to_big_endian(&mut arr);
		arr
	}
}

impl<'a> From<&'a [u8; 16]> for U128 {
	fn from(bytes: &[u8; 16]) -> Self {
		bytes[..].into()
	}
}

impl From<[u8; 16]> for U128 {
	fn from(bytes: [u8; 16]) -> Self {
		bytes[..].as_ref().into()
	}
}

impl From<U128> for [u8; 16] {
	fn from(number: U128) -> Self {
		let mut arr = [0u8; 16];
		number.to_big_endian(&mut arr);
		arr
	}
}

impl<'a> From<&'a [u8; 64]> for U512 {
	fn from(bytes: &[u8; 64]) -> Self {
		bytes[..].into()
	}
}

impl From<[u8; 64]> for U512 {
	fn from(bytes: [u8; 64]) -> Self {
		bytes[..].as_ref().into()
	}
}

impl From<U512> for [u8; 64] {
	fn from(number: U512) -> Self {
		let mut arr = [0u8; 64];
		number.to_big_endian(&mut arr);
		arr
	}
}

#[cfg(feature="heapsizeof")]
known_heap_size!(0, U128, U256);

#[cfg(test)]
mod tests {
	use uint::{U128, U256, U512};

	#[test]
	pub fn display_u128() {
		let expected = "340282366920938463463374607431768211455";
		let value = U128::MAX;
		assert_eq!(format!("{}", value), expected);
		assert_eq!(format!("{:?}", value), expected);
	}

	#[test]
	pub fn display_u256() {
		let expected = "115792089237316195423570985008687907853269984665640564039457584007913129639935";
		let value = U256::MAX;
		assert_eq!(format!("{}", value), expected);
		assert_eq!(format!("{:?}", value), expected);
	}

	#[test]
	pub fn display_u512() {
		let expected = "13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095";
		let value = U512::MAX;
		assert_eq!(format!("{}", value), expected);
		assert_eq!(format!("{:?}", value), expected);
	}
}

#[cfg(test)]
#[cfg(feature="std")]
mod std_tests {
	use uint::{U128, U256, U512};
	use std::str::FromStr;
	use super::FromDecStrErr;
	use std::u64::MAX;

	#[test]
	pub fn uint256_from() {
		let e = U256([10, 0, 0, 0]);

		// test unsigned initialization
		let ua = U256::from(10u8);
		let ub = U256::from(10u16);
		let uc = U256::from(10u32);
		let ud = U256::from(10u64);
		assert_eq!(e, ua);
		assert_eq!(e, ub);
		assert_eq!(e, uc);
		assert_eq!(e, ud);

		// test initialization from bytes
		let va = U256::from(&[10u8][..]);
		assert_eq!(e, va);

		// more tests for initialization from bytes
		assert_eq!(U256([0x1010, 0, 0, 0]), U256::from(&[0x10u8, 0x10][..]));
		assert_eq!(U256([0x12f0, 0, 0, 0]), U256::from(&[0x12u8, 0xf0][..]));
		assert_eq!(U256([0x12f0, 0, 0, 0]), U256::from(&[0, 0x12u8, 0xf0][..]));
		assert_eq!(U256([0x12f0, 0 , 0, 0]), U256::from(&[0, 0, 0, 0, 0, 0, 0, 0x12u8, 0xf0][..]));
		assert_eq!(U256([0x12f0, 1 , 0, 0]), U256::from(&[1, 0, 0, 0, 0, 0, 0, 0x12u8, 0xf0][..]));
		assert_eq!(
			U256([0x12f0, 1 , 0x0910203040506077, 0x8090a0b0c0d0e0f0]),
			U256::from(&
				[
					0x80, 0x90, 0xa0, 0xb0, 0xc0, 0xd0, 0xe0, 0xf0,
					0x09, 0x10, 0x20, 0x30, 0x40, 0x50, 0x60, 0x77,
					0, 0, 0, 0, 0, 0, 0, 1,
					0, 0, 0, 0, 0, 0, 0x12u8, 0xf0
				][..]
			)
		);
		assert_eq!(
			U256([0x00192437100019fa, 0x243710, 0, 0]),
			U256::from(&[0x24u8, 0x37, 0x10,0, 0x19, 0x24, 0x37, 0x10, 0, 0x19, 0xfa][..])
		);

		// test initializtion from string
		let sa = U256::from_str("0a").unwrap();
		assert_eq!(e, sa);
		assert_eq!(U256([0x1010, 0, 0, 0]), U256::from_str("1010").unwrap());
		assert_eq!(U256([0x12f0, 0, 0, 0]), U256::from_str("12f0").unwrap());
		assert_eq!(U256([0x12f0, 0, 0, 0]), U256::from_str("12f0").unwrap());
		assert_eq!(U256([0x12f0, 0 , 0, 0]), U256::from_str("0000000012f0").unwrap());
		assert_eq!(U256([0x12f0, 1 , 0, 0]), U256::from_str("0100000000000012f0").unwrap());
		assert_eq!(
			U256([0x12f0, 1 , 0x0910203040506077, 0x8090a0b0c0d0e0f0]),
			U256::from_str("8090a0b0c0d0e0f00910203040506077000000000000000100000000000012f0").unwrap()
		);
	}

	#[test]
	pub fn uint256_to() {
		let hex = "8090a0b0c0d0e0f00910203040506077583a2cf8264910e1436bda32571012f0";
		let uint = U256::from_str(hex).unwrap();
		let mut bytes = [0u8; 32];
		uint.to_big_endian(&mut bytes);
		let uint2 = U256::from(&bytes[..]);
		assert_eq!(uint, uint2);
	}

	#[test]
	pub fn uint256_bits_test() {
		assert_eq!(U256::from(0u64).bits(), 0);
		assert_eq!(U256::from(255u64).bits(), 8);
		assert_eq!(U256::from(256u64).bits(), 9);
		assert_eq!(U256::from(300u64).bits(), 9);
		assert_eq!(U256::from(60000u64).bits(), 16);
		assert_eq!(U256::from(70000u64).bits(), 17);

		//// Try to read the following lines out loud quickly
		let mut shl = U256::from(70000u64);
		shl = shl << 100;
		assert_eq!(shl.bits(), 117);
		shl = shl << 100;
		assert_eq!(shl.bits(), 217);
		shl = shl << 100;
		assert_eq!(shl.bits(), 0);

		//// Bit set check
		//// 01010
		assert!(!U256::from(10u8).bit(0));
		assert!(U256::from(10u8).bit(1));
		assert!(!U256::from(10u8).bit(2));
		assert!(U256::from(10u8).bit(3));
		assert!(!U256::from(10u8).bit(4));

		//// byte check
		assert_eq!(U256::from(10u8).byte(0), 10);
		assert_eq!(U256::from(0xffu64).byte(0), 0xff);
		assert_eq!(U256::from(0xffu64).byte(1), 0);
		assert_eq!(U256::from(0x01ffu64).byte(0), 0xff);
		assert_eq!(U256::from(0x01ffu64).byte(1), 0x1);
		assert_eq!(U256([0u64, 0xfc, 0, 0]).byte(8), 0xfc);
		assert_eq!(U256([0u64, 0, 0, u64::max_value()]).byte(31), 0xff);
		assert_eq!(U256([0u64, 0, 0, (u64::max_value() >> 8) + 1]).byte(31), 0x01);
	}

	#[test]
	#[cfg_attr(feature="dev", allow(eq_op))]
	pub fn uint256_comp_test() {
		let small = U256([10u64, 0, 0, 0]);
		let big = U256([0x8C8C3EE70C644118u64, 0x0209E7378231E632, 0, 0]);
		let bigger = U256([0x9C8C3EE70C644118u64, 0x0209E7378231E632, 0, 0]);
		let biggest = U256([0x5C8C3EE70C644118u64, 0x0209E7378231E632, 0, 1]);

		assert!(small < big);
		assert!(big < bigger);
		assert!(bigger < biggest);
		assert!(bigger <= biggest);
		assert!(biggest <= biggest);
		assert!(bigger >= big);
		assert!(bigger >= small);
		assert!(small <= small);
	}

	#[test]
	pub fn uint256_arithmetic_test() {
		let init = U256::from(0xDEADBEEFDEADBEEFu64);
		let copy = init;

		let add = init + copy;
		assert_eq!(add, U256([0xBD5B7DDFBD5B7DDEu64, 1, 0, 0]));
		// Bitshifts
		let shl = add << 88;
		assert_eq!(shl, U256([0u64, 0xDFBD5B7DDE000000, 0x1BD5B7D, 0]));
		let shr = shl >> 40;
		assert_eq!(shr, U256([0x7DDE000000000000u64, 0x0001BD5B7DDFBD5B, 0, 0]));
		// Increment
		let incr = shr + U256::from(1u64);
		assert_eq!(incr, U256([0x7DDE000000000001u64, 0x0001BD5B7DDFBD5B, 0, 0]));
		// Subtraction
		let sub = overflowing!(incr.overflowing_sub(init));
		assert_eq!(sub, U256([0x9F30411021524112u64, 0x0001BD5B7DDFBD5A, 0, 0]));
		// Multiplication
		let mult = sub.mul_u32(300);
		assert_eq!(mult, U256([0x8C8C3EE70C644118u64, 0x0209E7378231E632, 0, 0]));
		// Division
		assert_eq!(U256::from(105u8) / U256::from(5u8), U256::from(21u8));
		let div = mult / U256::from(300u16);
		assert_eq!(div, U256([0x9F30411021524112u64, 0x0001BD5B7DDFBD5A, 0, 0]));

		let a = U256::from_str("ff000000000000000000000000000000000000000000000000000000000000d1").unwrap();
		let b = U256::from_str("00ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff2e").unwrap();
		println!("{:x}", a);
		println!("{:x}", b);
		assert_eq!(!a, b);
		assert_eq!(a, !b);
	}

	#[test]
	pub fn uint256_simple_mul() {
		let a = U256::from_str("10000000000000000").unwrap();
		let b = U256::from_str("10000000000000000").unwrap();

		let c = U256::from_str("100000000000000000000000000000000").unwrap();
		println!("Multiplying");
		let result = a.overflowing_mul(b);
		println!("Got result");
		assert_eq!(result, (c, false))
	}

	#[test]
	pub fn uint256_extreme_bitshift_test() {
		//// Shifting a u64 by 64 bits gives an undefined value, so make sure that
		//// we're doing the Right Thing here
		let init = U256::from(0xDEADBEEFDEADBEEFu64);

		assert_eq!(init << 64, U256([0, 0xDEADBEEFDEADBEEF, 0, 0]));
		let add = (init << 64) + init;
		assert_eq!(add, U256([0xDEADBEEFDEADBEEF, 0xDEADBEEFDEADBEEF, 0, 0]));
		assert_eq!(add >> 0, U256([0xDEADBEEFDEADBEEF, 0xDEADBEEFDEADBEEF, 0, 0]));
		assert_eq!(add << 0, U256([0xDEADBEEFDEADBEEF, 0xDEADBEEFDEADBEEF, 0, 0]));
		assert_eq!(add >> 64, U256([0xDEADBEEFDEADBEEF, 0, 0, 0]));
		assert_eq!(add << 64, U256([0, 0xDEADBEEFDEADBEEF, 0xDEADBEEFDEADBEEF, 0]));
	}

	#[test]
	pub fn uint256_exp10() {
		assert_eq!(U256::exp10(0), U256::from(1u64));
		println!("\none: {:?}", U256::from(1u64));
		println!("ten: {:?}", U256::from(10u64));
		assert_eq!(U256::from(2u64) * U256::from(10u64), U256::from(20u64));
		assert_eq!(U256::exp10(1), U256::from(10u64));
		assert_eq!(U256::exp10(2), U256::from(100u64));
		assert_eq!(U256::exp10(5), U256::from(100000u64));
	}

	#[test]
	pub fn uint256_mul32() {
		assert_eq!(U256::from(0u64).mul_u32(2), U256::from(0u64));
		assert_eq!(U256::from(1u64).mul_u32(2), U256::from(2u64));
		assert_eq!(U256::from(10u64).mul_u32(2), U256::from(20u64));
		assert_eq!(U256::from(10u64).mul_u32(5), U256::from(50u64));
		assert_eq!(U256::from(1000u64).mul_u32(50), U256::from(50000u64));
	}

	#[test]
	fn uint256_pow() {
		assert_eq!(U256::from(10).pow(U256::from(0)), U256::from(1));
		assert_eq!(U256::from(10).pow(U256::from(1)), U256::from(10));
		assert_eq!(U256::from(10).pow(U256::from(2)), U256::from(100));
		assert_eq!(U256::from(10).pow(U256::from(3)), U256::from(1000));
		assert_eq!(U256::from(10).pow(U256::from(20)), U256::exp10(20));
	}

	#[test]
	#[should_panic]
	fn uint256_pow_overflow_panic() {
		U256::from(2).pow(U256::from(0x100));
	}

	#[test]
	fn should_format_hex_correctly() {
		assert_eq!(&U256::from(0).to_hex(), &"0");
		assert_eq!(&U256::from(0x1).to_hex(), &"1");
		assert_eq!(&U256::from(0xf).to_hex(), &"f");
		assert_eq!(&U256::from(0x10).to_hex(), &"10");
		assert_eq!(&U256::from(0xff).to_hex(), &"ff");
		assert_eq!(&U256::from(0x100).to_hex(), &"100");
		assert_eq!(&U256::from(0xfff).to_hex(), &"fff");
		assert_eq!(&U256::from(0x1000).to_hex(), &"1000");
	}

	#[test]
	fn uint256_overflowing_pow() {
		// assert_eq!(
		// 	U256::from(2).overflowing_pow(U256::from(0xff)),
		// 	(U256::from_str("8000000000000000000000000000000000000000000000000000000000000000").unwrap(), false)
		// );
		assert_eq!(
			U256::from(2).overflowing_pow(U256::from(0x100)),
			(U256::zero(), true)
		);
	}

	#[test]
	pub fn uint256_mul1() {
		assert_eq!(U256::from(1u64) * U256::from(10u64), U256::from(10u64));
	}

	#[test]
	pub fn uint256_mul2() {
		let a = U512::from_str("10000000000000000fffffffffffffffe").unwrap();
		let b = U512::from_str("ffffffffffffffffffffffffffffffff").unwrap();

		assert_eq!(a * b, U512::from_str("10000000000000000fffffffffffffffcffffffffffffffff0000000000000002").unwrap());
	}

	#[test]
	pub fn uint256_overflowing_mul() {
		assert_eq!(
			U256::from_str("100000000000000000000000000000000").unwrap().overflowing_mul(
				U256::from_str("100000000000000000000000000000000").unwrap()
			),
			(U256::zero(), true)
		);
	}

	#[test]
	pub fn uint128_add() {
		assert_eq!(
			U128::from_str("fffffffffffffffff").unwrap() + U128::from_str("fffffffffffffffff").unwrap(),
			U128::from_str("1ffffffffffffffffe").unwrap()
		);
	}

	#[test]
	pub fn uint128_add_overflow() {
		assert_eq!(
			U128::from_str("ffffffffffffffffffffffffffffffff").unwrap()
			.overflowing_add(
				U128::from_str("ffffffffffffffffffffffffffffffff").unwrap()
			),
			(U128::from_str("fffffffffffffffffffffffffffffffe").unwrap(), true)
		);
	}

	#[test]
	#[should_panic]
	#[cfg(debug_assertions)]
	pub fn uint128_add_overflow_panic() {
		let _res = U128::from_str("ffffffffffffffffffffffffffffffff").unwrap()
			+
			U128::from_str("ffffffffffffffffffffffffffffffff").unwrap();
	}

	#[test]
	pub fn uint128_mul() {
		assert_eq!(
			U128::from_str("fffffffff").unwrap() * U128::from_str("fffffffff").unwrap(),
			U128::from_str("ffffffffe000000001").unwrap());
	}

	#[test]
	pub fn uint512_mul() {
		assert_eq!(
			U512::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			*
			U512::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap(),
			U512::from_str("3fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000001").unwrap()
		);
	}

	#[test]
	pub fn uint256_mul_overflow() {
		assert_eq!(
			U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			.overflowing_mul(
				U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			),
			(U256::from_str("1").unwrap(), true)
		);
	}

	#[test]
	#[should_panic]
	pub fn uint256_mul_overflow_panic() {
		let _res = U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			*
			U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap();
	}

	#[test]
	pub fn uint256_sub_overflow() {
		assert_eq!(
			U256::from_str("0").unwrap()
			.overflowing_sub(
				U256::from_str("1").unwrap()
			),
			(U256::from_str("ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap(), true)
			);
	}

	#[test]
	#[should_panic]
	pub fn uint256_sub_overflow_panic() {
		let _res = U256::from_str("0").unwrap()
			-
			U256::from_str("1").unwrap();
	}

	#[test]
	pub fn uint256_shl() {
		assert_eq!(
			U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			<< 4,
			U256::from_str("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0").unwrap()
		);
	}

	#[test]
	pub fn uint256_shl_words() {
		assert_eq!(
			U256::from_str("0000000000000001ffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			<< 64,
			U256::from_str("ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000").unwrap()
		);
		assert_eq!(
			U256::from_str("0000000000000000ffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			<< 64,
			U256::from_str("ffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000").unwrap()
		);
	}

	#[test]
	pub fn uint256_mul() {
		assert_eq!(
			U256::from_str("7fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff").unwrap()
			*
			U256::from_str("2").unwrap(),
			U256::from_str("fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffe").unwrap()
			);
	}

	#[test]
	fn uint256_div() {
		assert_eq!(U256::from(10u64) /  U256::from(1u64), U256::from(10u64));
		assert_eq!(U256::from(10u64) /  U256::from(2u64), U256::from(5u64));
		assert_eq!(U256::from(10u64) /  U256::from(3u64), U256::from(3u64));
	}

	#[test]
	fn uint256_rem() {
		assert_eq!(U256::from(10u64) % U256::from(1u64), U256::from(0u64));
		assert_eq!(U256::from(10u64) % U256::from(3u64), U256::from(1u64));
	}

	#[test]
	fn uint256_from_dec_str() {
		assert_eq!(U256::from_dec_str("10").unwrap(), U256::from(10u64));
		assert_eq!(U256::from_dec_str("1024").unwrap(), U256::from(1024u64));
		assert_eq!(U256::from_dec_str("115792089237316195423570985008687907853269984665640564039457584007913129639936"), Err(FromDecStrErr::InvalidLength));
		assert_eq!(U256::from_dec_str("0x11"), Err(FromDecStrErr::InvalidCharacter));
	}

	#[test]
	fn display_uint() {
		let s = "12345678987654321023456789";
		assert_eq!(format!("{}", U256::from_dec_str(s).unwrap()), s);
	}

	#[test]
	fn display_uint_zero() {
		assert_eq!(format!("{}", U256::from(0)), "0");
	}

    #[test]
    fn u512_multi_adds() {
		let (result, _) = U512([0, 0, 0, 0, 0, 0, 0, 0]).overflowing_add(U512([0, 0, 0, 0, 0, 0, 0, 0]));
		assert_eq!(result, U512([0, 0, 0, 0, 0, 0, 0, 0]));

		let (result, _) = U512([1, 0, 0, 0, 0, 0, 0, 1]).overflowing_add(U512([1, 0, 0, 0, 0, 0, 0, 1]));
		assert_eq!(result, U512([2, 0, 0, 0, 0, 0, 0, 2]));

		let (result, _) = U512([0, 0, 0, 0, 0, 0, 0, 1]).overflowing_add(U512([0, 0, 0, 0, 0, 0, 0, 1]));
		assert_eq!(result, U512([0, 0, 0, 0, 0, 0, 0, 2]));

		let (result, _) = U512([0, 0, 0, 0, 0, 0, 2, 1]).overflowing_add(U512([0, 0, 0, 0, 0, 0, 3, 1]));
		assert_eq!(result, U512([0, 0, 0, 0, 0, 0, 5, 2]));

		let (result, _) = U512([1, 2, 3, 4, 5, 6, 7, 8]).overflowing_add(U512([9, 10, 11, 12, 13, 14, 15, 16]));
		assert_eq!(result, U512([10, 12, 14, 16, 18, 20, 22, 24]));

		let (_, overflow) = U512([0, 0, 0, 0, 0, 0, 2, 1]).overflowing_add(U512([0, 0, 0, 0, 0, 0, 3, 1]));
		assert!(!overflow);

		let (_, overflow) = U512([MAX, MAX, MAX, MAX, MAX, MAX, MAX, MAX])
			.overflowing_add(U512([MAX, MAX, MAX, MAX, MAX, MAX, MAX, MAX]));
		assert!(overflow);

		let (_, overflow) = U512([0, 0, 0, 0, 0, 0, 0, MAX])
			.overflowing_add(U512([0, 0, 0, 0, 0, 0, 0, MAX]));
        assert!(overflow);

		let (_, overflow) = U512([0, 0, 0, 0, 0, 0, 0, MAX])
			.overflowing_add(U512([0, 0, 0, 0, 0, 0, 0, 0]));
		assert!(!overflow);
	}

    #[test]
    fn u256_multi_adds() {
        let (result, _) = U256([0, 0, 0, 0]).overflowing_add(U256([0, 0, 0, 0]));
        assert_eq!(result, U256([0, 0, 0, 0]));

        let (result, _) = U256([0, 0, 0, 1]).overflowing_add(U256([0, 0, 0, 1]));
        assert_eq!(result, U256([0, 0, 0, 2]));

        let (result, overflow) = U256([0, 0, 2, 1]).overflowing_add(U256([0, 0, 3, 1]));
        assert_eq!(result, U256([0, 0, 5, 2]));
        assert!(!overflow);

        let (_, overflow) = U256([MAX, MAX, MAX, MAX])
			.overflowing_add(U256([MAX, MAX, MAX, MAX]));
        assert!(overflow);

        let (_, overflow) = U256([0, 0, 0, MAX]).overflowing_add(U256([0, 0, 0, MAX]));
        assert!(overflow);
    }


	#[test]
	fn u256_multi_subs() {
		let (result, _) = U256([0, 0, 0, 0]).overflowing_sub(U256([0, 0, 0, 0]));
		assert_eq!(result, U256([0, 0, 0, 0]));

		let (result, _) = U256([0, 0, 0, 1]).overflowing_sub(U256([0, 0, 0, 1]));
		assert_eq!(result, U256([0, 0, 0, 0]));

		let (_, overflow) = U256([0, 0, 2, 1]).overflowing_sub(U256([0, 0, 3, 1]));
		assert!(overflow);

		let (result, overflow) =
			U256([MAX, MAX, MAX, MAX])
				.overflowing_sub(U256([MAX/2, MAX/2, MAX/2, MAX/2]));

		assert!(!overflow);
		assert_eq!(U256([MAX/2+1, MAX/2+1, MAX/2+1, MAX/2+1]), result);

		let (result, overflow) = U256([0, 0, 0, 1]).overflowing_sub(U256([0, 0, 1, 0]));
		assert!(!overflow);
		assert_eq!(U256([0, 0, MAX, 0]), result);

		let (result, overflow) = U256([0, 0, 0, 1]).overflowing_sub(U256([1, 0, 0, 0]));
		assert!(!overflow);
		assert_eq!(U256([MAX, MAX, MAX, 0]), result);
	}

	#[test]
	fn u512_multi_subs() {
		let (result, _) = U512([0, 0, 0, 0, 0, 0, 0, 0]).overflowing_sub(U512([0, 0, 0, 0, 0, 0, 0, 0]));
		assert_eq!(result, U512([0, 0, 0, 0, 0, 0, 0, 0]));

		let (result, _) = U512([10, 9, 8, 7, 6, 5, 4, 3]).overflowing_sub(U512([9, 8, 7, 6, 5, 4, 3, 2]));
		assert_eq!(result, U512([1, 1, 1, 1, 1, 1, 1, 1]));

		let (_, overflow) = U512([10, 9, 8, 7, 6, 5, 4, 3]).overflowing_sub(U512([9, 8, 7, 6, 5, 4, 3, 2]));
		assert!(!overflow);

		let (_, overflow) = U512([9, 8, 7, 6, 5, 4, 3, 2]).overflowing_sub(U512([10, 9, 8, 7, 6, 5, 4, 3]));
		assert!(overflow);
	}

	#[test]
	fn u256_multi_carry_all() {
		let (result, _) = U256([MAX, 0, 0, 0]).overflowing_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U256([1, MAX-1, 0, 0]), result);

		let (result, _) = U256([0, MAX, 0, 0]).overflowing_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U256([0, 1, MAX-1, 0]), result);

		let (result, _) = U256([MAX, MAX, 0, 0]).overflowing_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U256([1, MAX, MAX-1, 0]), result);

		let (result, _) = U256([MAX, 0, 0, 0]).overflowing_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U256([1, MAX, MAX-1, 0]), result);

		let (result, _) = U256([MAX, MAX, 0, 0])
			.overflowing_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U256([1, 0, MAX-1, MAX]), result);

		let (result, _) = U256([MAX, 0, 0, 0]).overflowing_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U256([1, MAX, MAX, MAX-1]), result);

		let (result, _) = U256([MAX, MAX, MAX, 0]).overflowing_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U256([1, MAX, MAX, MAX-1]), result);

		let (result, _) = U256([MAX, 0, 0, 0]).overflowing_mul(
			U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U256([1, MAX, MAX, MAX]), result);

		let (result, _) = U256([MAX, MAX, MAX, MAX])
			.overflowing_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U256([1, MAX, MAX, MAX]), result);

		let (result, _) = U256([MAX, MAX, MAX, 0])
			.overflowing_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U256([1, 0, MAX, MAX-1]), result);

		let (result, _) = U256([MAX, MAX, 0, 0])
			.overflowing_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U256([1, 0, MAX, MAX-1]), result);

		let (result, _) = U256([MAX, MAX, MAX, MAX])
			.overflowing_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U256([1, 0, MAX, MAX]), result);

		let (result, _) = U256([MAX, MAX, 0, 0])
			.overflowing_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U256([1, 0, MAX, MAX]), result);

		let (result, _) = U256([MAX, MAX, MAX, 0])
			.overflowing_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U256([1, 0, 0, MAX-1]), result);

		let (result, _) = U256([MAX, MAX, MAX, 0])
			.overflowing_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U256([1, 0, 0, MAX]), result);

		let (result, _) = U256([MAX, MAX, MAX, MAX])
			.overflowing_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U256([1, 0, 0, MAX]), result);

		let (result, _) = U256([0, 0, 0, MAX]).overflowing_mul(U256([0, 0, 0, MAX]));
		assert_eq!(U256([0, 0, 0, 0]), result);

		let (result, _) = U256([1, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, MAX]));
		assert_eq!(U256([0, 0, 0, MAX]), result);

		let (result, _) = U256([MAX, MAX, MAX, MAX])
			.overflowing_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U256([1, 0, 0, 0]), result);
	}

	#[test]
	fn u256_multi_muls() {
		let (result, _) = U256([0, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 0]), result);

		let (result, _) = U256([1, 0, 0, 0]).overflowing_mul(U256([1, 0, 0, 0]));
		assert_eq!(U256([1, 0, 0, 0]), result);

		let (result, _) = U256([5, 0, 0, 0]).overflowing_mul(U256([5, 0, 0, 0]));
		assert_eq!(U256([25, 0, 0, 0]), result);

		let (result, _) = U256([0, 5, 0, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 0, 25, 0]), result);

		let (result, _) = U256([0, 0, 0, 1]).overflowing_mul(U256([1, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 1]), result);

		let (result, _) = U256([0, 0, 0, 5]).overflowing_mul(U256([2, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 10]), result);

		let (result, _) = U256([0, 0, 1, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 0, 0, 5]), result);

		let (result, _) = U256([0, 0, 8, 0]).overflowing_mul(U256([0, 0, 7, 0]));
		assert_eq!(U256([0, 0, 0, 0]), result);

		let (result, _) = U256([2, 0, 0, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 10, 0, 0]), result);

		let (result, _) = U256([1, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, MAX]));
		assert_eq!(U256([0, 0, 0, MAX]), result);
	}

    #[test]
    fn u256_multi_muls_overflow() {
		let (_, overflow) = U256([1, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, 0]));
		assert!(!overflow);

		let (_, overflow) = U256([1, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, MAX]));
		assert!(!overflow);

		let (_, overflow) = U256([0, 1, 0, 0]).overflowing_mul(U256([0, 0, 0, MAX]));
		assert!(overflow);

		let (_, overflow) = U256([0, 1, 0, 0]).overflowing_mul(U256([0, 1, 0, 0]));
		assert!(!overflow);

		let (_, overflow) = U256([0, 1, 0, MAX]).overflowing_mul(U256([0, 1, 0, MAX]));
		assert!(overflow);

		let (_, overflow) = U256([0, MAX, 0, 0]).overflowing_mul(U256([0, MAX, 0, 0]));
		assert!(!overflow);

		let (_, overflow) = U256([1, 0, 0, 0]).overflowing_mul(U256([10, 0, 0, 0]));
		assert!(!overflow);

		let (_, overflow) = U256([2, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, MAX / 2]));
		assert!(!overflow);

		let (_, overflow) = U256([0, 0, 8, 0]).overflowing_mul(U256([0, 0, 7, 0]));
		assert!(overflow);
    }

	#[test]
	fn big_endian() {
		let source = U256([1, 0, 0, 0]);
		let mut target = vec![0u8; 32];

		assert_eq!(source, U256::from(1));

		source.to_big_endian(&mut target);
		assert_eq!(
			vec![0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
				0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 1u8],
			target);

		let source = U256([512, 0, 0, 0]);
		let mut target = vec![0u8; 32];

		source.to_big_endian(&mut target);
		assert_eq!(
			vec![0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
				0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 2u8, 0u8],
			target);

		let source = U256([0, 512, 0, 0]);
		let mut target = vec![0u8; 32];

		source.to_big_endian(&mut target);
		assert_eq!(
			vec![0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8,
				0u8, 0u8, 0u8, 0u8, 0u8, 2u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8, 0u8],
			target);

		let source = U256::from_str("0102030405060708090a0b0c0d0e0f101112131415161718191a1b1c1d1e1f20").unwrap();
		source.to_big_endian(&mut target);
		assert_eq!(
			vec![0x01, 0x02, 0x03, 0x04, 0x05, 0x06, 0x07, 0x08, 0x09, 0x0a, 0x0b, 0x0c, 0x0d, 0x0e, 0x0f, 0x10, 0x11,
				0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18, 0x19, 0x1a, 0x1b, 0x1c, 0x1d, 0x1e, 0x1f, 0x20],
			target);
	}

	#[test]
	#[cfg_attr(feature="dev", allow(cyclomatic_complexity))]
	fn u256_multi_full_mul() {
		let result = U256([0, 0, 0, 0]).full_mul(U256([0, 0, 0, 0]));
		assert_eq!(U512([0, 0, 0, 0, 0, 0, 0, 0]), result);

		let result = U256([1, 0, 0, 0]).full_mul(U256([1, 0, 0, 0]));
		assert_eq!(U512([1, 0, 0, 0, 0, 0, 0, 0]), result);

		let result = U256([5, 0, 0, 0]).full_mul(U256([5, 0, 0, 0]));
		assert_eq!(U512([25, 0, 0, 0, 0, 0, 0, 0]), result);

		let result = U256([0, 5, 0, 0]).full_mul(U256([0, 5, 0, 0]));
		assert_eq!(U512([0, 0, 25, 0, 0, 0, 0, 0]), result);

		let result = U256([0, 0, 0, 4]).full_mul(U256([4, 0, 0, 0]));
		assert_eq!(U512([0, 0, 0, 16, 0, 0, 0, 0]), result);

		let result = U256([0, 0, 0, 5]).full_mul(U256([2, 0, 0, 0]));
		assert_eq!(U512([0, 0, 0, 10, 0, 0, 0, 0]), result);

		let result = U256([0, 0, 2, 0]).full_mul(U256([0, 5, 0, 0]));
		assert_eq!(U512([0, 0, 0, 10, 0, 0, 0, 0]), result);

		let result = U256([0, 3, 0, 0]).full_mul(U256([0, 0, 3, 0]));
		assert_eq!(U512([0, 0, 0, 9, 0, 0, 0, 0]), result);

		let result = U256([0, 0, 8, 0]).full_mul(U256([0, 0, 6, 0]));
		assert_eq!(U512([0, 0, 0, 0, 48, 0, 0, 0]), result);

		let result = U256([9, 0, 0, 0]).full_mul(U256([0, 3, 0, 0]));
		assert_eq!(U512([0, 27, 0, 0, 0, 0, 0, 0]), result);

		let result = U256([MAX, 0, 0, 0]).full_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U512([1, MAX-1, 0, 0, 0, 0, 0, 0]), result);

		let result = U256([0, MAX, 0, 0]).full_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U512([0, 1, MAX-1, 0, 0, 0, 0, 0]), result);

		let result = U256([MAX, MAX, 0, 0]).full_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U512([1, MAX, MAX-1, 0, 0, 0, 0, 0]), result);

		let result = U256([MAX, 0, 0, 0]).full_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U512([1, MAX, MAX-1, 0, 0, 0, 0, 0]), result);

		let result = U256([MAX, MAX, 0, 0]).full_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U512([1, 0, MAX-1, MAX, 0, 0, 0, 0]), result);

		let result = U256([MAX, 0, 0, 0]).full_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U512([1, MAX, MAX, MAX-1, 0, 0, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, 0]).full_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U512([1, MAX, MAX, MAX-1, 0, 0, 0, 0]), result);

		let result = U256([MAX, 0, 0, 0]).full_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U512([1, MAX, MAX, MAX, MAX-1, 0, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, MAX]).full_mul(U256([MAX, 0, 0, 0]));
		assert_eq!(U512([1, MAX, MAX, MAX, MAX-1, 0, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, 0]).full_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U512([1, 0, MAX, MAX-1, MAX, 0, 0, 0]), result);

		let result = U256([MAX, MAX, 0, 0]).full_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U512([1, 0, MAX, MAX-1, MAX, 0, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, MAX]).full_mul(U256([MAX, MAX, 0, 0]));
		assert_eq!(U512([1, 0, MAX, MAX, MAX-1, MAX, 0, 0]), result);

		let result = U256([MAX, MAX, 0, 0]).full_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U512([1, 0, MAX, MAX, MAX-1, MAX, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, 0]).full_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U512([1, 0, 0, MAX-1, MAX, MAX, 0, 0]), result);

		let result = U256([MAX, MAX, MAX, 0]).full_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U512([1, 0, 0, MAX,  MAX-1, MAX, MAX, 0]), result);

		let result = U256([MAX, MAX, MAX, MAX]).full_mul(U256([MAX, MAX, MAX, 0]));
		assert_eq!(U512([1, 0, 0, MAX,  MAX-1, MAX, MAX, 0]), result);

		let result = U256([MAX, MAX, MAX, MAX]).full_mul(U256([MAX, MAX, MAX, MAX]));
		assert_eq!(U512([1, 0, 0, 0, MAX-1, MAX, MAX, MAX]), result);

		let result = U256([0, 0, 0, MAX]).full_mul(U256([0, 0, 0, MAX]));
		assert_eq!(U512([0, 0, 0, 0, 0, 0, 1, MAX-1]), result);

		let result = U256([1, 0, 0, 0]).full_mul(U256([0, 0, 0, MAX]));
		assert_eq!(U512([0, 0, 0, MAX, 0, 0, 0, 0]), result);

		let result = U256([1, 2, 3, 4]).full_mul(U256([5, 0, 0, 0]));
		assert_eq!(U512([5, 10, 15, 20, 0, 0, 0, 0]), result);

		let result = U256([1, 2, 3, 4]).full_mul(U256([0, 6, 0, 0]));
		assert_eq!(U512([0, 6, 12, 18, 24, 0, 0, 0]), result);

		let result = U256([1, 2, 3, 4]).full_mul(U256([0, 0, 7, 0]));
		assert_eq!(U512([0, 0, 7, 14, 21, 28, 0, 0]), result);

		let result = U256([1, 2, 3, 4]).full_mul(U256([0, 0, 0, 8]));
		assert_eq!(U512([0, 0, 0, 8, 16, 24, 32, 0]), result);

		let result = U256([1, 2, 3, 4]).full_mul(U256([5, 6, 7, 8]));
		assert_eq!(U512([5, 16, 34, 60, 61, 52, 32, 0]), result);
	}

	#[test]
	fn u256_multi_muls2() {

		let (result, _) = U256([0, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 0]), result);

		let (result, _) = U256([1, 0, 0, 0]).overflowing_mul(U256([1, 0, 0, 0]));
		assert_eq!(U256([1, 0, 0, 0]), result);

		let (result, _) = U256([5, 0, 0, 0]).overflowing_mul(U256([5, 0, 0, 0]));
		assert_eq!(U256([25, 0, 0, 0]), result);

		let (result, _) = U256([0, 5, 0, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 0, 25, 0]), result);

		let (result, _) = U256([0, 0, 0, 1]).overflowing_mul(U256([1, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 1]), result);

		let (result, _) = U256([0, 0, 0, 5]).overflowing_mul(U256([2, 0, 0, 0]));
		assert_eq!(U256([0, 0, 0, 10]), result);

		let (result, _) = U256([0, 0, 1, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 0, 0, 5]), result);

		let (result, _) = U256([0, 0, 8, 0]).overflowing_mul(U256([0, 0, 7, 0]));
		assert_eq!(U256([0, 0, 0, 0]), result);

		let (result, _) = U256([2, 0, 0, 0]).overflowing_mul(U256([0, 5, 0, 0]));
		assert_eq!(U256([0, 10, 0, 0]), result);

		let (result, _) = U256([1, 0, 0, 0]).overflowing_mul(U256([0, 0, 0, u64::max_value()]));
		assert_eq!(U256([0, 0, 0, u64::max_value()]), result);

		let x1: U256 = "0000000000000000000000000000000000000000000000000000012365124623".into();
		let x2sqr_right: U256 = "000000000000000000000000000000000000000000014baeef72e0378e2328c9".into();
		let x1sqr = x1 * x1;
		assert_eq!(x2sqr_right, x1sqr);

		let x1cube = x1sqr * x1;
		let x1cube_right: U256 = "0000000000000000000000000000000001798acde139361466f712813717897b".into();
		assert_eq!(x1cube_right, x1cube);

		let x1quad = x1cube * x1;
		let x1quad_right: U256 = "000000000000000000000001adbdd6bd6ff027485484b97f8a6a4c7129756dd1".into();
		assert_eq!(x1quad_right, x1quad);

		let x1penta = x1quad * x1;
		let x1penta_right: U256 = "00000000000001e92875ac24be246e1c57e0507e8c46cc8d233b77f6f4c72993".into();
		assert_eq!(x1penta_right, x1penta);

		let x1septima = x1penta * x1;
		let x1septima_right: U256 = "00022cca1da3f6e5722b7d3cc5bbfb486465ebc5a708dd293042f932d7eee119".into();
		assert_eq!(x1septima_right, x1septima);
	}

	#[test]
	fn example() {
		let mut val: U256 = 1023.into();
		for _ in 0..200 { val = val * 2.into() }
		assert_eq!(&format!("{}", val), "1643897619276947051879427220465009342380213662639797070513307648");
	}

	#[test]
	fn little_endian() {
		let number: U256 = "00022cca1da3f6e5722b7d3cc5bbfb486465ebc5a708dd293042f932d7eee119".into();
		let expected = [
			0x19, 0xe1, 0xee, 0xd7,
			0x32, 0xf9, 0x42, 0x30,
			0x29, 0xdd, 0x08, 0xa7,
			0xc5, 0xeb, 0x65, 0x64,
			0x48, 0xfb, 0xbb, 0xc5,
			0x3c, 0x7d, 0x2b, 0x72,
			0xe5, 0xf6, 0xa3, 0x1d,
			0xca, 0x2c, 0x02, 0x00
		];
		let mut result = [0u8; 32];
		number.to_little_endian(&mut result);
		assert_eq!(expected, result);
	}

	#[test]
	fn slice_roundtrip() {
		let raw = [
			1u8, 2, 3, 5, 7, 11, 13, 17,
			19, 23, 29, 31, 37, 41, 43, 47,
			53, 59, 61, 67, 71, 73, 79, 83,
			89, 97, 101, 103, 107, 109, 113, 127
		];

		let u256: U256 = (&raw[..]).into();

		let mut new_raw = [0u8; 32];

		u256.to_big_endian(&mut new_raw);

		assert_eq!(&raw, &new_raw);
	}

	#[test]
	fn slice_roundtrip_le() {
		let raw = [
			1u8, 2, 3, 5, 7, 11, 13, 17,
			19, 23, 29, 31, 37, 41, 43, 47,
			53, 59, 61, 67, 71, 73, 79, 83,
			89, 97, 101, 103, 107, 109, 113, 127
		];

		let u256 = U256::from_little_endian(&raw[..]);

		let mut new_raw = [0u8; 32];

		u256.to_little_endian(&mut new_raw);

		assert_eq!(&raw, &new_raw);
	}

	#[test]
	fn slice_roundtrip_le2() {
		let raw = [
			2, 3, 5, 7, 11, 13, 17,
			19, 23, 29, 31, 37, 41, 43, 47,
			53, 59, 61, 67, 71, 73, 79, 83,
			89, 97, 101, 103, 107, 109, 113, 127
		];

		let u256 = U256::from_little_endian(&raw[..]);

		let mut new_raw = [0u8; 32];

		u256.to_little_endian(&mut new_raw);

		assert_eq!(&raw, &new_raw[..31]);
	}

	#[test]
	fn modular_inverse() {
		let modulo = U256::from_dec_str("115792089210356248762697446949407573530086143415290314195533631308867097853951").unwrap();
		let number = U256::from_dec_str("48439561293906451759052585252797914202762949526041747995844080717082404635286").unwrap();
		let mod_inv = number.mod_inverse(modulo);
		assert_eq!(
			mod_inv,
			U256::from_dec_str("101489101214698129329668954935570020318890663581888936938143465331216272806456").unwrap()
		)
	}

	#[test]
	fn fixed_arrays_roundtrip() {
		let raw: U256 = "7094875209347850239487502394881".into();
		let array: [u8; 32] = raw.into();
		let new_raw = array.into();

		assert_eq!(raw, new_raw);
	}

	#[test]
	fn from_little_endian() {
		let source: [u8; 32] = [
			1, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
		];

		let number = U256::from_little_endian(&source[..]);

		assert_eq!(U256::from(1), number);
	}

	#[test]
	fn from_big_endian() {
		let source: [u8; 32] = [
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 0,
			0, 0, 0, 0, 0, 0, 0, 1,
		];

		let number = U256::from_big_endian(&source[..]);

		assert_eq!(U256::from(1), number);
	}

	#[test]
	fn leading_zeros() {
		assert_eq!(U256::from("000000000000000000000001adbdd6bd6ff027485484b97f8a6a4c7129756dd1").leading_zeros(), 95);
		assert_eq!(U256::from("f00000000000000000000001adbdd6bd6ff027485484b97f8a6a4c7129756dd1").leading_zeros(), 0);
		assert_eq!(U256::from("0000000000000000000000000000000000000000000000000000000000000001").leading_zeros(), 255);
		assert_eq!(U256::from("0000000000000000000000000000000000000000000000000000000000000000").leading_zeros(), 256);
	}

	#[test]
	fn trailing_zeros() {
		assert_eq!(U256::from("1adbdd6bd6ff027485484b97f8a6a4c7129756dd100000000000000000000000").trailing_zeros(), 92);
		assert_eq!(U256::from("1adbdd6bd6ff027485484b97f8a6a4c7129756dd10000000000000000000000f").trailing_zeros(), 0);
		assert_eq!(U256::from("8000000000000000000000000000000000000000000000000000000000000000").trailing_zeros(), 255);
		assert_eq!(U256::from("0000000000000000000000000000000000000000000000000000000000000000").trailing_zeros(), 256);
	}

	mod laws {
		use uint::{U128, U256, U512};

		macro_rules! uint_arbitrary {
			($uint:ty, $n_bytes:tt) => {
				impl ::quickcheck::Arbitrary for $uint {
					fn arbitrary<G: ::quickcheck::Gen>(g: &mut G) -> Self {
						let mut res = [0u8; $n_bytes];

						let p = g.next_f64();
						let range =
							if p < 0.1 {
								$n_bytes
							} else if p < 0.2 {
								$n_bytes / 2
							} else {
								$n_bytes / 5
							};

						let size = g.gen_range(0, range);
						g.fill_bytes(&mut res[..size]);

						Self::from(res)
					}
				}
			}
		}

		uint_arbitrary!(U128, 16);
		uint_arbitrary!(U256, 32);
		uint_arbitrary!(U512, 64);

		macro_rules! o_try {
			($o:expr) => {{
				let (val, o) = $o;
				if o { return ::quickcheck::TestResult::discard(); }
				val
			}};
		}

		macro_rules! try_expr {
			($any:ident) => { $any };
			($first:ident + $($second:tt)*) => {
				o_try!($first.overflowing_add(try_expr!($($second)*)))
			};
			(($($anything:tt)*)) => {
				try_expr!($($anything)*)
			};
			($first:ident * $($second:tt)*) => {
				o_try!($first.overflowing_mul(try_expr!($($second)*)))
			};
			(($($first:tt)*) + $($rest:tt)*) => {{
				let first = try_expr!($($first)*);
				try_expr!(first + $($rest)*)
			}};
			(($($first:tt)*) * $($rest:tt)*) => {{
				let first = try_expr!($($first)*);
				try_expr!(first * $($rest)*)
			}};
		}

		macro_rules! uint_laws {
			($mod_name:ident, $uint_ty:ident) => {
				mod $mod_name {
					use quickcheck::TestResult;
					use uint::*;

					quickcheck! {
						fn associative_add(x: $uint_ty, y: $uint_ty, z: $uint_ty) -> TestResult {
							TestResult::from_bool(
								try_expr!((x + y) + z) ==
									try_expr!(x + (y + z))
							)
						}
					}

					quickcheck! {
						fn associative_mul(x: $uint_ty, y: $uint_ty, z: $uint_ty) -> TestResult {
							TestResult::from_bool(
								try_expr!((x * y) * z) == try_expr!(x * (y * z))
							)
						}
					}

					quickcheck! {
						fn commutative_add(x: $uint_ty, y: $uint_ty) -> TestResult {
							TestResult::from_bool(
								try_expr!(x + y) == try_expr!(y + x)
							)
						}
					}

					quickcheck! {
						fn commutative_mul(x: $uint_ty, y: $uint_ty) -> TestResult {
							TestResult::from_bool(
								try_expr!(x * y) == try_expr!(y * x)
							)
						}
					}

					quickcheck! {
						fn identity_add(x: $uint_ty) -> bool {
							x + $uint_ty::zero() == x
						}
					}

					quickcheck! {
						fn identity_mul(x: $uint_ty) -> bool {
							x * $uint_ty::one() == x
						}
					}

					quickcheck! {
						fn identity_div(x: $uint_ty) -> bool {
							x / $uint_ty::one() == x
						}
					}

					quickcheck! {
						fn absorbing_rem(x: $uint_ty) -> bool {
							x % $uint_ty::one() == $uint_ty::zero()
						}
					}

					quickcheck! {
						fn absorbing_sub(x: $uint_ty) -> bool {
							x - x == $uint_ty::zero()
						}
					}

					quickcheck! {
						fn absorbing_mul(x: $uint_ty) -> bool {
							x * $uint_ty::zero() == $uint_ty::zero()
						}
					}

					quickcheck! {
						fn distributive_mul_over_add(x: $uint_ty, y: $uint_ty, z: $uint_ty) -> TestResult {
							TestResult::from_bool(
								try_expr!(x * (y + z)) == try_expr!((x * y) + (x * z)) &&
									try_expr!((x + y) * z) == try_expr!((x * z) + (y * z))
							)
						}
					}

					quickcheck! {
						fn pow_mul(x: $uint_ty) -> TestResult {
							let (p2, o) = x.overflowing_pow($uint_ty::from(2));
							if o { return TestResult::discard(); }
							let (p3, o) = x.overflowing_pow($uint_ty::from(3));
							if o { return TestResult::discard(); }

							TestResult::from_bool(
								p2 == x * x && p3 == x * x * x
							)
						}
					}

					quickcheck! {
						fn add_increases(x: $uint_ty, y: $uint_ty) -> TestResult {
							if y.is_zero() {
								return TestResult::discard();
							}

							TestResult::from_bool(
								try_expr!(x + y) > x
							)
						}
					}

					quickcheck! {
						fn mul_increases(x: $uint_ty, y: $uint_ty) -> TestResult {
							if y.is_zero() {
								return TestResult::discard();
							}

							TestResult::from_bool(
								try_expr!(x * y) >= x
							)
						}
					}

					quickcheck! {
						fn div_decreases_dividend(x: $uint_ty, y: $uint_ty) -> TestResult {
							if y.is_zero() {
								return TestResult::discard();
							}

							TestResult::from_bool(
								x / y <= x
							)
						}
					}

					quickcheck! {
						fn rem_decreases_divisor(x: $uint_ty, y: $uint_ty) -> TestResult {
							if y.is_zero() {
								return TestResult::discard();
							}

							TestResult::from_bool(
								x % y < y
							)
						}
					}
				}
			}
		}

		uint_laws!(u128, U128);
		uint_laws!(u256, U256);
		uint_laws!(u512, U512);
	}
}
