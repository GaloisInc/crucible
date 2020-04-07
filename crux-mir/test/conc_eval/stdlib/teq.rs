#![cfg_attr(not(with_main), no_std)]

pub trait PPE<Rhs: ?Sized = Self> {
        fn peq(&self, other: &Rhs) -> bool;
        fn pne(&self, other: &Rhs) -> bool; // { !self.eq(other) }
}

pub trait PEq: PPE<Self> {}

pub enum O {
        /// An ordering where a compared value is greater [than another].
        G = 1,
        /// An ordering where a compared value is equal [to another].
        E = 0,
        /// An ordering where a compared value is less [than another].
        L= -1,

}

use O::*;

impl PPE for O {
    fn peq(&self, _other:&Self) -> bool { false }
    fn pne(&self, other: &Self) -> bool { !self.peq(other) }
} 
    
impl PEq for O {} 

fn g<T:PEq>(y : T) -> bool {
    y.peq(&y)
}

fn f (_y : u32) -> bool { 
    let x: O = G;
    x.peq(&x) && g(x)
    
}

const ARG: u32 = 1;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> bool { f(ARG) }
