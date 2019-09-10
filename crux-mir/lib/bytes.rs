use std::io;
use std::marker::PhantomData;


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
}

impl BytesMut {
    pub fn new() -> BytesMut {
        unimplemented!()
    }

    pub fn len(&self) -> usize {
        unimplemented!()
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
