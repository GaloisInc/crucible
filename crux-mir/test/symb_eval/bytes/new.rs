#![cfg_attr(not(with_main), no_std)]

extern crate bytes;
use bytes::{Bytes, BytesMut, Buf, BufMut};

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut b = BytesMut::new();
    assert!(b.len() == 0);
    assert!(b.is_empty());
    assert!(b.freeze().len() == 0);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
