#![cfg_attr(not(with_main), no_std)]
#[cfg(not(with_main))] extern crate std;

use std::io::{Cursor, Read, Write};

pub fn f(x: u8) -> u8 {
    let mut buf = [0; 5];
    let msg = b"hello, world!";

    let mut c = Cursor::new(msg);
    c.read(&mut buf);

    for (a, b) in buf.iter().zip(msg.iter()) {
        assert!(a == b);
    }

    0
}

pub static ARG: u8 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u8 { f(ARG) }
