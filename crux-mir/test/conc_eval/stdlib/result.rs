#![cfg_attr(not(with_main), no_std)]
// This tests using polymorphic functions and parameterized data

pub enum Opt<T> {
    N,
    S(T),
}

pub enum Res<T, E> {
        /// Contains the success value
        O(T),

        /// Contains the error value
        E(E),
    }


use Opt::*;
use Res::*;

pub fn map<T,E,U, F: FnOnce(T) -> U>(x:Res<T,E>, op: F) -> Res<U,E> {
    match x {
        O(t) => O(op(t)),
        E(e) => E(e)
    }
} 


pub fn g<T,U>(y : Res<T,U>) -> Opt<T> {
    match y {
        O(x)  => S(x),
        E(_) => N,
    } 
}

fn f (x : u32) -> u32 {
    let z : Res<u32,u32> = O(x);
    match g(z) {
        S (y) => return y,
        N => return 0
    }
}

const ARG : u32 = 27;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
