use std::io;
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
