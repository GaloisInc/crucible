#![cfg_attr(not(with_main), no_std)]

#[cfg(not(with_main))] extern crate std;
#[cfg(not(with_main))] use std::boxed::Box;
#[cfg(not(with_main))] use std::string::String;

fn move_out(x: Box<String>) -> String {
    *x
}

#[cfg_attr(crux, crux::test)]
pub fn f() {
    let s: String = "Hello, World!".into();
    let b = Box::new(s.clone());
    assert!(move_out(b) == s);
}


#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
