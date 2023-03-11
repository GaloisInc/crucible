#![cfg_attr(not(with_main), no_std)]
#![feature(never_type)]

extern crate core;

fn f(x:u16) -> bool {
   let mut buf  = [0,0];
   let res1 = x.ser(&mut buf);
    match res1 {
        Some(v) => true,
        None => false,
    }

}

const ARG: u16 = 1;

/////////////////////////////////////////////////////////////////////


pub trait Lmcp where Self : Sized {
    fn ser(&self, buf : &mut[u8]) -> Option<usize>;
}

impl Lmcp for u16 {
    fn ser(&self, buf: &mut[u8]) -> Option<usize> {
        let m = buf.get_mut(0..2).unwrap();
        m[0] = (*self >> 8) as u8;
        m[1] = *self as u8;
        Some(2)
    }
}


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> bool { f(ARG) }
