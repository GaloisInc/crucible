#![cfg_attr(not(with_main), no_std)]

// Test Associated Type translation when type parameters have predicates mentioning other parameters.
//
pub enum Opt<T> {
    /// No value
    N,
    /// Some value `T`
    S(T)
}

use Opt::*;

pub trait A {
    type I;
    fn n(&mut self) -> Opt<Self::I>;
}

pub trait B {
    type K : A <I=Self::J>;
    type J ;
    fn into_i(self) -> Self::K;
}

impl A for i32 {
    type I = u8 ;
    fn n(&mut self) -> Opt<u8> {
        N
    }
}

impl B for [u8; 3] {
    type J = u8;
    type K = i32;
    fn into_i(self) -> i32 {
        0
    }
}



fn f (_y : u32) -> i32 {
    let x : [u8;3] = [1,2,3];
    let mut i = x.into_i();
    i.n();
    i
}


const ARG: u32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> i32 { f(ARG) }
