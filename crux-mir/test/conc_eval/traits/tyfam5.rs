#![cfg_attr(not(with_main), no_std)]
pub enum Opt<T> {
    /// No value
    N,
    /// Some value `T`
    S(T)
}

use Opt::*;

pub trait Ir {
    type Item;
    fn dummy(x:Self::Item) -> Self::Item;
}

impl<T: Ir> Ir for Opt<T> {
    type Item = <T as Ir>::Item;
    fn dummy(x:Self::Item) -> Self::Item { x }
}

impl Ir for i32 {
    type Item = u8;
    fn dummy(x:Self::Item) -> Self::Item { x}
}

// Stub to avoid "Could not find cfg: f"
const ARG: i32 = 1;
fn f(arg: i32) {

}


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
