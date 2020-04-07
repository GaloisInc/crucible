#![cfg_attr(not(with_main), no_std)]
#[cfg(not(with_main))] extern crate std;
extern crate byteorder;

use std::io::{Cursor, Read, Write};
use byteorder::*;

pub fn f(x: u8) -> u8 {
    let mut buf = [0_u8; 7];
    let mut c = Cursor::new(&mut buf as &mut [_]);

    let x = c.write_u16::<LE>(0x6261).unwrap();
    let y = c.write_u32::<BE>(0x63646566).unwrap();
    let z = c.write_u8(0x67).unwrap();

    let goal = *b"abcdefg";
    for i in 0 .. 7 {
        assert!(buf[i] == goal[i]);
    }

    0
}

pub static ARG: u8 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u8 { f(ARG) }
