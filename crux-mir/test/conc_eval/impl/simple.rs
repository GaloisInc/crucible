#![cfg_attr(not(with_main), no_std)]
enum S {}

impl S {
    fn g() -> u32 {
        42
    }
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
