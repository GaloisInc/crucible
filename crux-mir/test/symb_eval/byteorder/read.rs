#![cfg_attr(not(with_main), no_std)]
#[cfg(not(with_main))] extern crate std;
extern crate byteorder;

use std::io::{Cursor, Read, Write};
use byteorder::*;

pub fn f(x: u8) -> u8 {
    let mut buf = *b"abcdefg";
    let mut c = Cursor::new(&buf);

    let x = c.read_u16::<LE>().unwrap();
    let y = c.read_u32::<BE>().unwrap();
    let z = c.read_u8().unwrap();

    assert!(x == 0x6261);
    assert!(y == 0x63646566);
    assert!(z == 0x67);

    0
}

pub static ARG: u8 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux::test] fn crux_test() -> u8 { f(ARG) }
