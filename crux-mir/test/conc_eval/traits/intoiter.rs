
pub enum Opt<T> {
    /// No value
    N,
    /// Some value `T`
    S(T)
}

use Opt::*;

pub trait Iter {
    type Item;
    fn n(&mut self) -> Opt<Self::Item>;
}

pub trait IntoI {
    type Item;
    type IntoIter: Iter<Item=Self::Item>;
    fn into_i(self) -> Self::IntoIter;
}

impl Iter for isize {
    type Item = u8 ;
    fn n(&mut self) -> Opt<u8> {
        N
    }
}

impl IntoI for &[u8] {
    type Item = u8;
    type IntoIter = isize;
    fn into_i(self) -> isize {
        0
    }
}



fn f (_y : u32) -> isize { 
    let x : &[u8] = &[1,2,3];
    let mut i = x.into_i();
    i.n();
    i
}


const ARG: u32 = 1;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
