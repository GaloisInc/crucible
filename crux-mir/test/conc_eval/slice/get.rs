#![feature(never_type)]

use std::process::exit;

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

macro_rules! get {
    ( $e:expr ) => {
        $e.unwrap_or_else(||exit(0))
    }
}

impl Lmcp for u16 {
    fn ser(&self, buf: &mut[u8]) -> Option<usize> {
        let m = get!(buf.get_mut(0..2));
        m[0] = (*self >> 8) as u8;
        m[1] = *self as u8;
        Some(2)
    }
}


#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
