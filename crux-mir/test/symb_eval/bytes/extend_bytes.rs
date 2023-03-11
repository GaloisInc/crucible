#![no_std]

extern crate bytes;
use bytes::{Bytes, BytesMut, Buf, BufMut};

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let mut bm = BytesMut::with_capacity(10);
    let b = Bytes::from(b"12345" as &[_]);
    bm.extend(&b);
}
