#![cfg_attr(not(with_main), no_std)]

fn g () -> char {
    'a'
}

fn h () -> () {
    ()
}

fn f (x : i32) -> () {
    h ();
}

const ARG : i32 = 0;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
