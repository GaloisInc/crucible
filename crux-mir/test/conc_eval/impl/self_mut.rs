#![cfg_attr(not(with_main), no_std)]
struct S {
    x: u32,
}

impl S {
    fn g(&mut self) {
        self.x += 1;
    }
}

fn f(_: ()) -> u32 {
    let mut s = S { x: 41 };
    s.g();
    s.x
}

const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> u32 { f(ARG) }
