#![cfg_attr(not(with_main), no_std)]

extern crate bytes;
use bytes::{Bytes, BytesMut, Buf, BufMut};

#[crux_test]
pub fn f() {
    let mut b = BytesMut::with_capacity(10);
    b.put_u8(1);
    b.put_u16_be(0x0203);
    assert!(b.len() == 3);
    assert!(b[0] == 1);
    assert!(b[1] == 2);
    assert!(b[2] == 3);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
