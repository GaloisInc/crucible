//! Arithmetic mod \\(2\^{252} + 27742317777372353535851937790883648493\\)
//! with five \\(52\\)-bit unsigned limbs.
//!
//! \\(51\\)-bit limbs would cover the desired bit range (\\(253\\)
//! bits), but isn't large enough to reduce a \\(512\\)-bit number with
//! Montgomery multiplication, so \\(52\\) bits is used instead.  To see
//! that this is safe for intermediate results, note that the largest
//! limb in a \\(5\times 5\\) product of \\(52\\)-bit limbs will be
//!
//! ```text
//! (0xfffffffffffff^2) * 5 = 0x4ffffffffffff60000000000005 (107 bits).
//! ```

//use core::fmt::Debug;
use std::ops::{Index, IndexMut};



use self::integer::Integer;

mod integer {
    use std::ops::{Add, Sub, Mul, Div, Rem, BitAnd, BitOr, BitXor, Shl, Shr};
    use std::cmp::{Ord, PartialOrd, Ordering};
    #[derive(Copy)]
    pub struct Integer {}

    pub fn clone(_i: &Integer) -> Integer { unimplemented!() }
    impl Clone for Integer {
        fn clone(&self) -> Integer { clone(self) }
    }

    pub fn symbolic(_x: &'static str) -> Integer { ::std::process::exit(0) }
    impl Integer {
        pub fn symbolic(x: &'static str) -> Integer { symbolic(x) }

        pub fn L() -> Integer {
            add(shl(self::i32::from_prim(1), 252),
                // This 128-bit constant has to be split into two parts, since u128 literals don't
                // work properly yet (they get truncated to 64 bits).
                bitor(
                    self::u64::from_prim(0x5812631a5cf5d3ed),
                    shl(self::u64::from_prim(0x14def9dea2f79cd6), 64)))
        }
    }

    macro_rules! binop {
        ($Op:ident, $op:ident) => {
            pub fn $op(_x: Integer, _y: Integer) -> Integer { unimplemented!() }

            impl $Op<Integer> for Integer {
                type Output = Integer;
                fn $op(self, other: Integer) -> Integer { $op(self, other) }
            }
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
            pub fn $op(_x: Integer, _bits: u32) -> Integer { unimplemented!() }

            /*
            impl $Op<u32> for Integer {
                type Output = Integer;
                fn $op(self, bits: u32) -> Integer { $op(self, bits) }
            }
            */
        };
    }
    shift_op!(Shl, shl);
    shift_op!(Shr, shr);

    pub fn eq(_x: Integer, _y: Integer) -> bool { unimplemented!() }
    /*
    impl PartialEq for Integer {
        fn eq(&self, other: &Integer) -> bool { eq(*self, *other) }
        fn ne(&self, other: &Integer) -> bool { !eq(*self, *other) }
    }
    impl Eq for Integer {}
    */

    pub fn lt(_x: Integer, _y: Integer) -> bool { unimplemented!() }
    /*
    impl PartialOrd for Integer {
        fn partial_cmp(&self, other: &Integer) -> Option<Ordering> {
            Some(self.cmp(other))
        }
    }
    impl Ord for Integer {
        fn cmp(&self, other: &Integer) -> Ordering {
            if eq(*self, *other) { Ordering::Equal }
            else if lt(*self, *other) { Ordering::Less }
            else { Ordering::Greater }
        }
    }
    */

    macro_rules! prim_cast {
        ($Prim:ident) => {
            pub mod $Prim {
                use super::Integer;
                pub fn from_prim(_x: $Prim) -> Integer { unimplemented!() }
                pub fn as_prim(_x: Integer) -> $Prim { unimplemented!() }
            }

            /*
            impl From<$Prim> for Integer {
                fn from(x: $Prim) -> Integer { self::$Prim::from_prim(x) }
            }

            impl From<Integer> for $Prim {
                fn from(x: Integer) -> $Prim { self::$Prim::as_prim(x) }
            }
            */
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

    pub fn from_scalar(x: super::Scalar64) -> Integer {
        let mut acc = self::i32::from_prim(0);
        for i in 0..5 {
            acc = bitor(acc, shl(self::u64::from_prim(x.0[i]), 52 * i as u32));
        }
        acc
    }

    pub fn as_scalar(x: Integer) -> super::Scalar64 {
        let mut acc = super::Scalar64([0; 5]);
        let mask: Integer = self::u64::from_prim((1_u64 << 52) - 1);
        for i in 0..5 {
            acc.0[i] = self::u64::as_prim(bitand(shr(x, 52 * i as u32), mask));
        }
        acc
    }

    /// Check if an integer is in the range `0 .. L`.
    pub fn is_valid(x: Integer) -> bool {
        (lt(self::i32::from_prim(0), x) || eq(self::i32::from_prim(0), x)) &&
            lt(x, Integer::L())
    }
}

/*
impl From<Scalar64> for Integer {
    fn from(x: Scalar64) -> Integer {
        integer::from_scalar(x)
    }
}

impl From<Integer> for Scalar64 {
    fn from(x: Integer) -> Scalar64 {
        integer::as_scalar(x)
    }
}
*/

fn crucible_u64(_x: &'static str) -> u64 { unimplemented!() }

macro_rules! crucible_scalar64 {
    ($desc:expr) => {
        Scalar64([
            $crate::crucible_u64(concat!($desc, "_0")),
            $crate::crucible_u64(concat!($desc, "_1")),
            $crate::crucible_u64(concat!($desc, "_2")),
            $crate::crucible_u64(concat!($desc, "_3")),
            $crate::crucible_u64(concat!($desc, "_4")),
        ])
    };
}

#[allow(unused_variables)]
fn crucible_assert_impl(
    cond: bool,
    cond_str: &'static str,
    file: &'static str,
    line: u32,
    col: u32,
) -> () {
    ()
}

#[allow(unused_variables)]
fn crucible_assume_impl(
    cond: bool,
    cond_str: &'static str,
    file: &'static str,
    line: u32,
    col: u32,
) -> () {
    ()
}

macro_rules! crucible_assert {
    ($e:expr) => {
        crucible_assert_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

macro_rules! crucible_assume {
    ($e:expr) => {
        crucible_assume_impl($e, stringify!($e), file!(), line!(), column!())
    };
}

macro_rules! crucible_debug_integer {
    ($e:expr) => { crucible_debug_integer!($e, stringify!($e)) };
    ($e:expr, $desc:expr) => {
        crucible_assume!(integer::eq($e, integer::symbolic($desc)))
    };
}



#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}

fn f(_w : u64 ) -> bool {
    let zero = integer::i32::from_prim(0);

    // `integer::as/from_scalar` is a bijection on the integers `0 .. L`.
    {
        let i = integer::symbolic("isi");
        crucible_assume!(integer::is_valid(i));
        let s = integer::as_scalar(i);
        let i2 = integer::from_scalar(s);
        crucible_assert!(integer::eq(i2, i));
    }

    {
        let s = crucible_scalar64!("sis");
        for i in 0..5 {
            crucible_assume!(s.0[i] < 1 << 52);
        }
        let i = integer::from_scalar(s);
        let s2 = integer::as_scalar(i);
        for i in 0..5 {
            crucible_assert!(s2.0[i] == s.0[i]);
        }
    }

    // `Scalar64::add` correctly implements addition modulo `L`.
    {
        let a = integer::symbolic("add_a");
        let b = integer::symbolic("add_b");
        crucible_assume!(integer::is_valid(a));
        crucible_assume!(integer::is_valid(b));

        let s_a = integer::as_scalar(a);
        let s_b = integer::as_scalar(b);
        let s_y = Scalar64::add(&s_a, &s_b);

        let y = integer::from_scalar(s_y);
        // We'd like to say `y == (a + b) % L`, but the solver can't handle it (times out).
        // Instead, we assert a slightly stronger claim, which does not mention `%`:
        //      1. 0 <= y < L
        //      2. y == a + b  OR  y == a + b - L
        // This implies the original claim because we already know 0 <= a + b < 2 * L.
        crucible_assert!(integer::is_valid(y));
        crucible_assert!(
            integer::eq(y, integer::add(a, b)) ||
            integer::eq(y, integer::sub(integer::add(a, b), Integer::L()))
        );
    }

    return true;
}

const ARG: u64 = 20;





mod constants {
    use Scalar64;
    
    /// `L` is the order of base point, i.e. 2^252 + 27742317777372353535851937790883648493
    pub(crate) const L: Scalar64 = Scalar64([ 0x0002631a5cf5d3ed, 0x000dea2f79cd6581, 0x000000000014def9, 0x0000000000000000, 0x0000100000000000 ]);

    /// `L` * `LFACTOR` = -1 (mod 2^52)
    pub(crate) const LFACTOR: u64 = 0x51da312547e1b;

    /// `R` = R % L where R = 2^260
    pub(crate) const R: Scalar64 = Scalar64([ 0x000f48bd6721e6ed, 0x0003bab5ac67e45a, 0x000fffffeb35e51b, 0x000fffffffffffff, 0x00000fffffffffff ]);

    /// `RR` = (R^2) % L where R = 2^260
    pub(crate) const RR: Scalar64 = Scalar64([ 0x0009d265e952d13b, 0x000d63c715bea69f, 0x0005be65cb687604, 0x0003dceec73d217f, 0x000009411b7c309a ]);
}




/// The `Scalar64` struct represents an element in
/// \\(\mathbb Z / \ell \mathbb Z\\) as 5 \\(52\\)-bit limbs.
#[derive(Copy, Clone)]
pub struct Scalar64(pub [u64; 5]);

/*
impl Debug for Scalar64 {
    fn fmt(&self, f: &mut ::core::fmt::Formatter) -> ::core::fmt::Result {
        write!(f, "Scalar64: {:?}", &self.0[..])
    }
}*/

impl Index<usize> for Scalar64 {
    type Output = u64;
    fn index(&self, _index: usize) -> &u64 {
        &(self.0[_index])
    }
}

impl IndexMut<usize> for Scalar64 {
    fn index_mut(&mut self, _index: usize) -> &mut u64 {
        &mut (self.0[_index])
    }
}

/// u64 * u64 = u128 multiply helper
#[inline(always)]
fn m(x: u64, y: u64) -> u128 {
    (x as u128) * (y as u128)
}

impl Scalar64 {
    /// Return the zero scalar
    pub fn zero() -> Scalar64 {
        Scalar64([0,0,0,0,0])
    }

    /*
    /// Unpack a 32 byte / 256 bit scalar into 5 52-bit limbs.
    pub fn from_bytes(bytes: &[u8; 32]) -> Scalar64 {
        let mut words = [0u64; 4];
        for i in 0..4 {
            for j in 0..8 {
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;
        let top_mask = (1u64 << 48) - 1;
        let mut s = Scalar64::zero();

        s[ 0] =   words[0]                            & mask;
        s[ 1] = ((words[0] >> 52) | (words[1] << 12)) & mask;
        s[ 2] = ((words[1] >> 40) | (words[2] << 24)) & mask;
        s[ 3] = ((words[2] >> 28) | (words[3] << 36)) & mask;
        s[ 4] =  (words[3] >> 16)                     & top_mask;

        s
    }

    /// Reduce a 64 byte / 512 bit scalar mod l
    pub fn from_bytes_wide(bytes: &[u8; 64]) -> Scalar64 {
        let mut words = [0u64; 8];
        for i in 0..8 {
            for j in 0..8 {
                words[i] |= (bytes[(i * 8) + j] as u64) << (j * 8);
            }
        }

        let mask = (1u64 << 52) - 1;
        let mut lo = Scalar64::zero();
        let mut hi = Scalar64::zero();

        lo[0] =   words[ 0]                             & mask;
        lo[1] = ((words[ 0] >> 52) | (words[ 1] << 12)) & mask;
        lo[2] = ((words[ 1] >> 40) | (words[ 2] << 24)) & mask;
        lo[3] = ((words[ 2] >> 28) | (words[ 3] << 36)) & mask;
        lo[4] = ((words[ 3] >> 16) | (words[ 4] << 48)) & mask;
        hi[0] =  (words[ 4] >>  4)                      & mask;
        hi[1] = ((words[ 4] >> 56) | (words[ 5] <<  8)) & mask;
        hi[2] = ((words[ 5] >> 44) | (words[ 6] << 20)) & mask;
        hi[3] = ((words[ 6] >> 32) | (words[ 7] << 32)) & mask;
        hi[4] =   words[ 7] >> 20                             ;

        lo = Scalar64::montgomery_mul(&lo, &constants::R);  // (lo * R) / R = lo
        hi = Scalar64::montgomery_mul(&hi, &constants::RR); // (hi * R^2) / R = hi * R

        Scalar64::add(&hi, &lo)
    }

    /// Pack the limbs of this `Scalar64` into 32 bytes
    pub fn to_bytes(&self) -> [u8; 32] {
        let mut s = [0u8; 32];

        s[0]  =  (self.0[ 0] >>  0)                      as u8;
        s[1]  =  (self.0[ 0] >>  8)                      as u8;
        s[2]  =  (self.0[ 0] >> 16)                      as u8;
        s[3]  =  (self.0[ 0] >> 24)                      as u8;
        s[4]  =  (self.0[ 0] >> 32)                      as u8;
        s[5]  =  (self.0[ 0] >> 40)                      as u8;
        s[6]  = ((self.0[ 0] >> 48) | (self.0[ 1] << 4)) as u8;
        s[7]  =  (self.0[ 1] >>  4)                      as u8;
        s[8]  =  (self.0[ 1] >> 12)                      as u8;
        s[9]  =  (self.0[ 1] >> 20)                      as u8;
        s[10] =  (self.0[ 1] >> 28)                      as u8;
        s[11] =  (self.0[ 1] >> 36)                      as u8;
        s[12] =  (self.0[ 1] >> 44)                      as u8;
        s[13] =  (self.0[ 2] >>  0)                      as u8;
        s[14] =  (self.0[ 2] >>  8)                      as u8;
        s[15] =  (self.0[ 2] >> 16)                      as u8;
        s[16] =  (self.0[ 2] >> 24)                      as u8;
        s[17] =  (self.0[ 2] >> 32)                      as u8;
        s[18] =  (self.0[ 2] >> 40)                      as u8;
        s[19] = ((self.0[ 2] >> 48) | (self.0[ 3] << 4)) as u8;
        s[20] =  (self.0[ 3] >>  4)                      as u8;
        s[21] =  (self.0[ 3] >> 12)                      as u8;
        s[22] =  (self.0[ 3] >> 20)                      as u8;
        s[23] =  (self.0[ 3] >> 28)                      as u8;
        s[24] =  (self.0[ 3] >> 36)                      as u8;
        s[25] =  (self.0[ 3] >> 44)                      as u8;
        s[26] =  (self.0[ 4] >>  0)                      as u8;
        s[27] =  (self.0[ 4] >>  8)                      as u8;
        s[28] =  (self.0[ 4] >> 16)                      as u8;
        s[29] =  (self.0[ 4] >> 24)                      as u8;
        s[30] =  (self.0[ 4] >> 32)                      as u8;
        s[31] =  (self.0[ 4] >> 40)                      as u8;

        s
    }
    */

    /// Compute `a + b` (mod l)
    pub fn add(a: &Scalar64, b: &Scalar64) -> Scalar64 {
        let mut sum = Scalar64::zero();
        let mask = (1u64 << 52) - 1;

        // a + b
        let mut carry: u64 = 0;
        for i in 0..5 {
            carry = a.0[i] + b.0[i] + (carry >> 52);
            sum.0[i] = carry & mask;
        }

        // subtract l if the sum is >= l
        Scalar64::sub(&sum, &constants::L)
    }

    /// Compute `a - b` (mod l)
    pub fn sub(a: &Scalar64, b: &Scalar64) -> Scalar64 {
        let mut difference = Scalar64::zero();
        let mask = (1u64 << 52) - 1;

        // a - b
        let mut borrow: u64 = 0;
        for i in 0..5 {
            borrow = a.0[i].wrapping_sub(b.0[i] + (borrow >> 63));
            difference.0[i] = borrow & mask;
        }

        // conditionally add l if the difference is negative
        let underflow_mask = ((borrow >> 63) ^ 1).wrapping_sub(1);
        let mut carry: u64 = 0;
        for i in 0..5 {
            carry = (carry >> 52) + difference.0[i] + (constants::L.0[i] & underflow_mask);
            difference.0[i] = carry & mask;
        }

        difference
    }

    /*
    /// Compute `a * b`
    #[inline(always)]
    pub (crate) fn mul_internal(a: &Scalar64, b: &Scalar64) -> [u128; 9] {
        let mut z = [0u128; 9];

        z[0] = m(a[0],b[0]);
        z[1] = m(a[0],b[1]) + m(a[1],b[0]);
        z[2] = m(a[0],b[2]) + m(a[1],b[1]) + m(a[2],b[0]);
        z[3] = m(a[0],b[3]) + m(a[1],b[2]) + m(a[2],b[1]) + m(a[3],b[0]);
        z[4] = m(a[0],b[4]) + m(a[1],b[3]) + m(a[2],b[2]) + m(a[3],b[1]) + m(a[4],b[0]);
        z[5] =                m(a[1],b[4]) + m(a[2],b[3]) + m(a[3],b[2]) + m(a[4],b[1]);
        z[6] =                               m(a[2],b[4]) + m(a[3],b[3]) + m(a[4],b[2]);
        z[7] =                                              m(a[3],b[4]) + m(a[4],b[3]);
        z[8] =                                                             m(a[4],b[4]);

        z
    }

    /// Compute `a^2`
    #[inline(always)]
    fn square_internal(a: &Scalar64) -> [u128; 9] {
        let aa = [
            a[0]*2,
            a[1]*2,
            a[2]*2,
            a[3]*2,
        ];

        [
            m( a[0],a[0]),
            m(aa[0],a[1]),
            m(aa[0],a[2]) + m( a[1],a[1]),
            m(aa[0],a[3]) + m(aa[1],a[2]),
            m(aa[0],a[4]) + m(aa[1],a[3]) + m( a[2],a[2]),
                            m(aa[1],a[4]) + m(aa[2],a[3]),
                                            m(aa[2],a[4]) + m( a[3],a[3]),
                                                            m(aa[3],a[4]),
                                                                            m(a[4],a[4])
        ]
    }

    /// Compute `limbs/R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(always)]
    pub (crate) fn montgomery_reduce(limbs: &[u128; 9]) -> Scalar64 {

        #[inline(always)]
        fn part1(sum: u128) -> (u128, u64) {
            let p = (sum as u64).wrapping_mul(constants::LFACTOR) & ((1u64 << 52) - 1);
            ((sum + m(p,constants::L[0])) >> 52, p)
        }

        #[inline(always)]
        fn part2(sum: u128) -> (u128, u64) {
            let w = (sum as u64) & ((1u64 << 52) - 1);
            (sum >> 52, w)
        }

        // note: l3 is zero, so its multiplies can be skipped
        let l = &constants::L;

        // the first half computes the Montgomery adjustment factor n, and begins adding n*l to make limbs divisible by R
        let (carry, n0) = part1(        limbs[0]);
        let (carry, n1) = part1(carry + limbs[1] + m(n0,l[1]));
        let (carry, n2) = part1(carry + limbs[2] + m(n0,l[2]) + m(n1,l[1]));
        let (carry, n3) = part1(carry + limbs[3]              + m(n1,l[2]) + m(n2,l[1]));
        let (carry, n4) = part1(carry + limbs[4] + m(n0,l[4])              + m(n2,l[2]) + m(n3,l[1]));

        // limbs is divisible by R now, so we can divide by R by simply storing the upper half as the result
        let (carry, r0) = part2(carry + limbs[5]              + m(n1,l[4])              + m(n3,l[2]) + m(n4,l[1]));
        let (carry, r1) = part2(carry + limbs[6]                           + m(n2,l[4])              + m(n4,l[2]));
        let (carry, r2) = part2(carry + limbs[7]                                        + m(n3,l[4])             );
        let (carry, r3) = part2(carry + limbs[8]                                                     + m(n4,l[4]));
        let         r4 = carry as u64;

        // result may be >= l, so attempt to subtract l
        Scalar64::sub(&Scalar64([r0,r1,r2,r3,r4]), l)
    }

    /// Compute `a * b` (mod l)
    #[inline(never)]
    pub fn mul(a: &Scalar64, b: &Scalar64) -> Scalar64 {
        let ab = Scalar64::montgomery_reduce(&Scalar64::mul_internal(a, b));
        Scalar64::montgomery_reduce(&Scalar64::mul_internal(&ab, &constants::RR))
    }

    /// Compute `a^2` (mod l)
    #[inline(never)]
    #[allow(dead_code)] // XXX we don't expose square() via the Scalar API
    pub fn square(&self) -> Scalar64 {
        let aa = Scalar64::montgomery_reduce(&Scalar64::square_internal(self));
        Scalar64::montgomery_reduce(&Scalar64::mul_internal(&aa, &constants::RR))
    }

    /// Compute `(a * b) / R` (mod l), where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_mul(a: &Scalar64, b: &Scalar64) -> Scalar64 {
        Scalar64::montgomery_reduce(&Scalar64::mul_internal(a, b))
    }

    /// Compute `(a^2) / R` (mod l) in Montgomery form, where R is the Montgomery modulus 2^260
    #[inline(never)]
    pub fn montgomery_square(&self) -> Scalar64 {
        Scalar64::montgomery_reduce(&Scalar64::square_internal(self))
    }

    /// Puts a Scalar64 in to Montgomery form, i.e. computes `a*R (mod l)`
    #[inline(never)]
    pub fn to_montgomery(&self) -> Scalar64 {
        Scalar64::montgomery_mul(self, &constants::RR)
    }

    /// Takes a Scalar64 out of Montgomery form, i.e. computes `a/R (mod l)`
    #[inline(never)]
    pub fn from_montgomery(&self) -> Scalar64 {
        let mut limbs = [0u128; 9];
        for i in 0..5 {
            limbs[i] = self[i] as u128;
        }
        Scalar64::montgomery_reduce(&limbs)
    }
    */
}




