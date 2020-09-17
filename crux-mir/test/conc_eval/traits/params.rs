#![cfg_attr(not(with_main), no_std)]
pub trait T {
    fn def () -> Self;
}

pub trait U<Rhs: ?Sized=Self> {
    fn bin(&self,other: &Rhs) -> bool;
}


impl T for i32 {
    fn def () -> i32 { 25 }
}

impl U<i32> for i32 {
    fn bin(&self,other:&Self) -> bool { *self == *other }
}


fn f(x : i32) -> i32 {
    if x.bin(&x) {
        i32::def()
    } else {
        33
    }
}

const ARG: i32 = 12;

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> i32 { f(ARG) }
