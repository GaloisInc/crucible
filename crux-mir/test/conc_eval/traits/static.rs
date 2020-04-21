#![cfg_attr(not(with_main), no_std)]
// We match the type of S::g against T::g.  But g's type
// does not include 'Self' so there is no information to be gained.

enum S {}

trait T {
    fn g() -> u32;
}

impl T for S {
    fn g() -> u32 { 42 }
}

fn f(_: ()) -> u32 {
    S::g()
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> u32 { f(ARG) }
