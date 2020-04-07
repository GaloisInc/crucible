#![cfg_attr(not(with_main), no_std)]
// Test trait with default implementation
//

trait T {
    fn m (&self) -> i32;

    fn g (&self) -> i32 { 42 }
}


impl T for i32 {
    fn m (&self) -> i32 { *self }
}

fn f(x : i32) -> i32 {
    x.m()
}

const ARG: i32 = 12;

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { f(ARG) }
