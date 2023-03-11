#![cfg_attr(not(with_main), no_std)]
// Test two static implementation of the same trait
//
// We match the type of S::g and U::g against T::g.  But g's type
// does not include 'Self' so there is no information to be gained.
//
// We need more info from mir-json to make progress: Issue #4



enum S {}
enum U {}

trait T {
    fn g() -> u32;
}

impl T for S {
    fn g() -> u32 { 42 }
}

impl T for U {
    fn g() -> u32 { 1 }
}

fn f(_: ()) -> u32 {
    U::g()
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> u32 { f(ARG) }
