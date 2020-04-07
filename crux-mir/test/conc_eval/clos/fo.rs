#![cfg_attr(not(with_main), no_std)]

#![feature(type_ascription)]

fn f (y:i32) -> i32 {
    let z = 12;
    let w = 13;
    
    let g = |x:i32| x + y + z + w;

    g((1 :i32))

}

const ARG :i32 = 3;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
