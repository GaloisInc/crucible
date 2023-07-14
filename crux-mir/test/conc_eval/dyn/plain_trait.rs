#![cfg_attr(not(with_main), no_std)]

trait Tr {
    fn f(&self) -> i32;
}

struct St(i32);

impl Tr for St {
    fn f(&self) -> i32 { self.0 }
}


pub fn f(x: i32) -> i32 {
    let st = St(100);
    let tr: &dyn Tr = &st;
    tr.f()
}

pub static ARG: i32 = 1;

#[cfg(with_main)] pub fn main() { println!("{:?}", f(ARG)); }
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
