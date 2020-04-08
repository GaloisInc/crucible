#![no_std]

extern crate bytes;
#[macro_use] extern crate crucible;
use bytes::{Bytes, BytesMut, Buf, BufMut};
use core::ops::Deref;

#[cfg_attr(crux, crux_test)]
pub fn f() {
    let mut b = BytesMut::with_capacity(10);
    b.put_u8(1);

    let len = crucible::crucible_u8("len") as usize;
    crucible_assume!(len <= 8);
    for i in 0 .. len {
        b.put_u8(i as u8);
    }
    crucible_assert!(b.len() == 1 + len);

    let b2 = b.freeze();
    crucible_assert!(b2.len() == 1 + len);
    crucible_assert!(b2[0] == 1);
    if len > 0 {
        crucible_assert!(b2[1] == 0);
        crucible_assert!(b2[len] == len as u8 - 1);
    }
}
