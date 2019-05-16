// FAIL: error translating Deref impls
use std::ops::Deref;

struct S;

impl Deref for S {
    type Target = S;
    fn deref(&self) -> &S {
        static THE_S: S = S;
        &THE_S
    }
}

const ARG: i32 = 1;
fn f(arg: i32) {
}

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
