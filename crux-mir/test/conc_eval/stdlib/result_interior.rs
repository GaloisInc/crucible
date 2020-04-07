#![cfg_attr(not(with_main), no_std)]
pub enum Res<T, E> {
        /// Contains the success value
        O(T),

        /// Contains the error value
        E(E),
    }


use Res::*;

impl <T, E> Res<T,E> {
    
    pub fn as_mut(&mut self) -> Res<&mut T, &mut E> {
        match *self {
           O(ref mut x) => O(x),
           E(ref mut x) => E(x),
        }
    }
}    


fn f (x : u32) -> u32 {
    let mut z : Res<u32,u32> = O(x);
    let mut w = z.as_mut();
    let y = match w {
        O (ref mut x) => x,
        E (ref mut y) => y
    };
    **y = 3;
    match w {
        O (x) => *x,
        E (y) => *y
    }
        
}

const ARG : u32 = 27;


#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
