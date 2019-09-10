use std::io;
use std::iter::Extend;
use std::marker::PhantomData;
use std::mem;
use std::ops::{Deref, DerefMut};


#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct Bytes {
    _dummy: usize,
}

#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct BytesMut {
    _dummy: usize,
}

pub struct Writer<T> {
    _dummy: usize,
    _marker: PhantomData<T>,
}


impl Bytes {
    pub fn len(&self) -> usize {
        unimplemented!()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn split_off(&mut self, at: usize) -> Bytes {
        unimplemented!()
    }

    pub fn split_to(&mut self, at: usize) -> Bytes {
        let other = self.split_off(at);
        mem::replace(self, other)
    }
}

impl BytesMut {
    pub fn new() -> BytesMut {
        Self::with_capacity(0)
    }

    pub fn with_capacity(cap: usize) -> BytesMut {
        unimplemented!()
    }

    pub fn len(&self) -> usize {
        unimplemented!()
    }

    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    pub fn freeze(self) -> Bytes {
        unimplemented!()
    }

    pub fn reserve(&mut self, amt: usize) {
        unimplemented!()
    }
}


pub trait Buf {
}

pub trait BufMut {
    fn put_slice(&mut self, xs: &[u8]);

    fn put_u8(&mut self, x: u8) {
        unimplemented!()
    }

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
    where Self: Sized {
        unimplemented!()
    }
}


impl Buf for Bytes {
}

impl Buf for BytesMut {
}

impl BufMut for BytesMut {
    fn put_slice(&mut self, xs: &[u8]) {
        self.extend(xs);
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
        unimplemented!()
    }
}

impl io::Write for Writer<BytesMut> {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        unimplemented!()
    }

    fn flush(&mut self) -> io::Result<()> {
        unimplemented!()
    }
}

impl Deref for Bytes {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unimplemented!()
    }
}

impl Deref for BytesMut {
    type Target = [u8];
    fn deref(&self) -> &[u8] {
        unimplemented!()
    }
}

impl DerefMut for BytesMut {
    fn deref_mut(&mut self) -> &mut [u8] {
        unimplemented!()
    }
}

impl From<&[u8]> for Bytes {
    fn from(x: &[u8]) -> Bytes {
        unimplemented!()
    }
}

impl From<&[u8]> for BytesMut {
    fn from(x: &[u8]) -> BytesMut {
        unimplemented!()
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
    _dummy: usize,
}

impl IntoIterator for Bytes {
    type Item = u8;
    type IntoIter = Iter;
    fn into_iter(self) -> Iter {
        unimplemented!()
    }
}

impl Iterator for Iter {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        unimplemented!()
    }
}

