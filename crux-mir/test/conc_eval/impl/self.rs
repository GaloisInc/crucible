#![cfg_attr(not(with_main), no_std)]
struct S {
    x: u32,
}

impl S {
    fn g(&self) -> u32 {
        self.x + 1
    }
}

fn f(_: ()) -> u32 {
    let s = S { x: 41 };
    s.g()
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
