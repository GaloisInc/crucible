#![cfg_attr(not(with_main), no_std)]

extern crate bytes;
use bytes::{Bytes, BytesMut, Buf, BufMut};

#[crux::test]
pub fn f() {
    let mut b = BytesMut::with_capacity(0);
    b.put_slice(b"1234567-1234567-1234567-1234567-1234567-1234567-");
}
