#![cfg_attr(not(with_main), no_std)]

extern crate bytes;
use bytes::{Bytes, BytesMut, Buf, BufMut};

#[crux::test]
pub fn f() {
    let mut b = BytesMut::with_capacity(10);
    b.put_u32_be(0x01020304);
    let mut b = b.freeze();
    let b2 = b.split_off(2);
    assert!(b.len() == 2);
    assert!(b[0] == 1);
    assert!(b[1] == 2);
    assert!(b2.len() == 2);
    assert!(b2[0] == 3);
    assert!(b2[1] == 4);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
