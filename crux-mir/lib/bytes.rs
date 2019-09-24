//! Verifier-friendly implementations of the `Bytes` and `BytesMut` types from the `bytes` crate.
//! The implementation plays some tricks to provide some support for buffers of symbolic length,
//! even though the underlying `Vector` type requires the length to be concrete.  See the doc
//! comments on `Bytes`, `BytesMut`, `reserve`, and `crux_set_fixed` for details.

extern crate crucible;

use std::cmp::{self, Ordering};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::io;
use std::iter::Extend;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};

use crucible::vector::Vector;


/// A view into a byte array.  The underlying data is stored in a `Vector<u8>` of concrete size,
/// but the start and end can be symbolic.
#[derive(Clone)]
pub struct Bytes {
    data: Vector<u8>,
    start: usize,
    end: usize,
}

/// An owned, mutable byte array.  The capacity, which is the size of the underlying `Vector<u8>`,
/// is always concrete, but the `len` can be symbolic.  Only the first `len` bytes of `data` are
/// considered to be initialized.
#[derive(Clone)]
pub struct BytesMut {
    data: Vector<u8>,
    len: usize,
    /// When `true`, the capacity cannot actually grow.  Useful when calling code that may try to
    /// `reserve` a symbolic amount of capacity.
    crux_fixed: bool,
}


impl Bytes {
    pub fn len(&self) -> usize {
        self.end - self.start
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn split_off(&mut self, at: usize) -> Bytes {
        let mid = self.start + at;
        let end = self.end;
        self.end = mid;
        Bytes { data: self.data, start: mid, end }
    }

    pub fn split_to(&mut self, at: usize) -> Bytes {
        let start = self.start;
        let mid = self.start + at;
        self.start = mid;
        Bytes { data: self.data, start, end: mid }
    }
}

impl BytesMut {
    pub fn new() -> BytesMut {
        Self::with_capacity(0)
    }

    pub fn with_capacity(cap: usize) -> BytesMut {
        BytesMut {
            data: Vector::replicate(0, cap),
            len: 0,
            crux_fixed: false,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Freeze the contents of this buffer, producing a read-only view.
    pub fn freeze(self) -> Bytes {
        Bytes { data: self.data, start: 0, end: self.len }
    }

    pub fn reserve(&mut self, amt: usize) {
        if !self.crux_fixed {
            let excess = self.data.len() - self.len;
            if amt > excess {
                let more = amt - excess;
                self.data = self.data.concat(Vector::replicate(0, more));
            }
        }
    }

    pub fn truncate(&mut self, len: usize) {
        self.len = cmp::min(len, self.len);
    }

    pub fn crux_set_fixed(&mut self, fixed: bool) {
        self.crux_fixed = fixed;
    }
}


pub trait Buf {
}

pub trait BufMut {
    fn put_slice(&mut self, xs: &[u8]);

    fn put_u8(&mut self, x: u8);

    fn put_u16_be(&mut self, x: u16) {
        self.put_slice(&x.to_be_bytes())
    }

    fn put_u32_be(&mut self, x: u32) {
        self.put_slice(&x.to_be_bytes())
    }

    fn put_u64_be(&mut self, x: u64) {
        self.put_slice(&x.to_be_bytes())
    }

    fn put_u128_be(&mut self, x: u128) {
        self.put_slice(&x.to_be_bytes())
    }

    fn put_u16_le(&mut self, x: u16) {
        self.put_slice(&x.to_le_bytes())
    }

    fn put_u32_le(&mut self, x: u32) {
        self.put_slice(&x.to_le_bytes())
    }

    fn put_u64_le(&mut self, x: u64) {
        self.put_slice(&x.to_le_bytes())
    }

    fn put_u128_le(&mut self, x: u128) {
        self.put_slice(&x.to_le_bytes())
    }

    fn put_i8(&mut self, x: i8) {
        self.put_u8(x as u8)
    }

    fn put_i16_be(&mut self, x: i16) {
        self.put_u16_be(x as u16)
    }

    fn put_i32_be(&mut self, x: i32) {
        self.put_u32_be(x as u32)
    }

    fn put_i64_be(&mut self, x: i64) {
        self.put_u64_be(x as u64)
    }

    fn put_i128_be(&mut self, x: i128) {
        self.put_u128_be(x as u128)
    }

    fn put_i16_le(&mut self, x: i16) {
        self.put_u16_le(x as u16)
    }

    fn put_i32_le(&mut self, x: i32) {
        self.put_u32_le(x as u32)
    }

    fn put_i64_le(&mut self, x: i64) {
        self.put_u64_le(x as u64)
    }

    fn put_i128_le(&mut self, x: i128) {
        self.put_u128_le(x as u128)
    }

    fn writer(self) -> Writer<Self>
    where Self: Sized;
}


impl Buf for Bytes {
}

impl Buf for BytesMut {
}

impl BufMut for BytesMut {
    fn put_slice(&mut self, xs: &[u8]) {
        assert!(xs.len() <= self.data.len() - self.len,
            "not enough capacity for put_slice");
        self.data.as_mut_slice()[self.len .. self.len + xs.len()].copy_from_slice(xs);
        self.len += xs.len();
    }

    fn put_u8(&mut self, x: u8) {
        assert!(1 <= self.data.len() - self.len,
            "not enough capacity for put_u8");
        self.data.as_mut_slice()[self.len] = x;
        self.len += 1;
    }

    fn writer(self) -> Writer<Self>
    where Self: Sized {
        Writer {
            inner: self,
        }
    }
}

impl<T: BufMut> BufMut for &mut T {
    fn put_slice(&mut self, xs: &[u8]) {
        <T as BufMut>::put_slice(self, xs)
    }

    fn put_u8(&mut self, x: u8) {
        <T as BufMut>::put_u8(self, x)
    }

    fn writer(self) -> Writer<Self>
    where Self: Sized {
        Writer {
            inner: self,
        }
    }
}


impl PartialEq for Bytes {
    fn eq(&self, other: &Bytes) -> bool {
        <[u8] as PartialEq>::eq(self, other)
    }
    fn ne(&self, other: &Bytes) -> bool {
        <[u8] as PartialEq>::ne(self, other)
    }
}

impl PartialOrd for Bytes {
    fn partial_cmp(&self, other: &Bytes) -> Option<Ordering> {
        <[u8] as PartialOrd>::partial_cmp(self, other)
    }
    fn lt(&self, other: &Bytes) -> bool {
        <[u8] as PartialOrd>::lt(self, other)
    }
    fn le(&self, other: &Bytes) -> bool {
        <[u8] as PartialOrd>::le(self, other)
    }
    fn gt(&self, other: &Bytes) -> bool {
        <[u8] as PartialOrd>::gt(self, other)
    }
    fn ge(&self, other: &Bytes) -> bool {
        <[u8] as PartialOrd>::ge(self, other)
    }
}

impl Eq for Bytes {}

impl Ord for Bytes {
    fn cmp(&self, other: &Bytes) -> Ordering {
        <[u8] as Ord>::cmp(self, other)
    }
}

impl fmt::Debug for Bytes {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[u8] as fmt::Debug>::fmt(self, fmt)
    }
}

impl Hash for Bytes {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <[u8] as Hash>::hash(self, state)
    }
}

impl Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.data.as_slice()[self.start .. self.end]
    }
}


impl PartialEq for BytesMut {
    fn eq(&self, other: &BytesMut) -> bool {
        <[u8] as PartialEq>::eq(self, other)
    }
    fn ne(&self, other: &BytesMut) -> bool {
        <[u8] as PartialEq>::ne(self, other)
    }
}

impl PartialOrd for BytesMut {
    fn partial_cmp(&self, other: &BytesMut) -> Option<Ordering> {
        <[u8] as PartialOrd>::partial_cmp(self, other)
    }
    fn lt(&self, other: &BytesMut) -> bool {
        <[u8] as PartialOrd>::lt(self, other)
    }
    fn le(&self, other: &BytesMut) -> bool {
        <[u8] as PartialOrd>::le(self, other)
    }
    fn gt(&self, other: &BytesMut) -> bool {
        <[u8] as PartialOrd>::gt(self, other)
    }
    fn ge(&self, other: &BytesMut) -> bool {
        <[u8] as PartialOrd>::ge(self, other)
    }
}

impl Eq for BytesMut {}

impl Ord for BytesMut {
    fn cmp(&self, other: &BytesMut) -> Ordering {
        <[u8] as Ord>::cmp(self, other)
    }
}

impl fmt::Debug for BytesMut {
    fn fmt(&self, fmt: &mut fmt::Formatter<'_>) -> fmt::Result {
        <[u8] as fmt::Debug>::fmt(self, fmt)
    }
}

impl Hash for BytesMut {
    fn hash<H: Hasher>(&self, state: &mut H) {
        <[u8] as Hash>::hash(self, state)
    }
}

impl Deref for BytesMut {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        &self.data.as_slice()[.. self.len]
    }
}

impl DerefMut for BytesMut {
    fn deref_mut(&mut self) -> &mut [u8] {
        &mut self.data.as_mut_slice()[.. self.len]
    }
}


impl From<&[u8]> for Bytes {
    fn from(x: &[u8]) -> Bytes {
        Bytes {
            data: Vector::copy_from_slice(x),
            start: 0,
            end: x.len(),
        }
    }
}

impl From<&[u8]> for BytesMut {
    fn from(x: &[u8]) -> BytesMut {
        BytesMut {
            data: Vector::copy_from_slice(x),
            len: x.len(),
            crux_fixed: false,
        }
    }
}

impl Extend<u8> for BytesMut {
    fn extend<I: IntoIterator<Item = u8>>(&mut self, iter: I) {
        for x in iter {
            self.put_u8(x);
        }
    }
}

impl<'a> Extend<&'a u8> for BytesMut {
    fn extend<I: IntoIterator<Item = &'a u8>>(&mut self, iter: I) {
        for &x in iter {
            self.put_u8(x);
        }
    }
}

pub struct Iter {
    data: Vector<u8>,
    idx: usize,
    end: usize,
}

impl IntoIterator for Bytes {
    type Item = u8;
    type IntoIter = Iter;
    fn into_iter(self) -> Iter {
        Iter {
            data: self.data,
            idx: self.start,
            end: self.end,
        }
    }
}

impl IntoIterator for &Bytes {
    type Item = u8;
    type IntoIter = Iter;
    fn into_iter(self) -> Iter {
        Iter {
            data: self.data,
            idx: self.start,
            end: self.end,
        }
    }
}

impl Iterator for Iter {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.idx < self.end {
            let val = self.data.as_slice()[self.idx];
            self.idx += 1;
            Some(val)
        } else {
            None
        }
    }
}


pub struct Writer<T> {
    inner: T,
}

impl<T: BufMut> io::Write for Writer<T> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        self.inner.put_slice(buf);
        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
