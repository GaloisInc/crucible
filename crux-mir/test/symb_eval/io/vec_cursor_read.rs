#![no_std]
#[macro_use] extern crate crucible;
extern crate std;
use std::io::{Read, Write, Cursor};
use std::vec::Vec;

#[crux_test]
pub fn f() {
    let mut buf = Vec::new();
    buf.write(&[1, 2, 3]);

    let mut curs = Cursor::new(buf);
    let mut rbuf = [0; 2];
    curs.read(&mut rbuf).unwrap();
    crucible_assert!(rbuf[0] == 1);
    crucible_assert!(rbuf[1] == 2);
}
