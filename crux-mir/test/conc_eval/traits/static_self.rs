#![cfg_attr(not(with_main), no_std)]
struct S(u32);

trait T {
    fn g(&self) -> u32;
}

impl T for S {
    fn g(&self) -> u32 { self.0 }
}

fn f(s: S) -> u32 {
    s.g()
}

const ARG: S = S(42);

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
