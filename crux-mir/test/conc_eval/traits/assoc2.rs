#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
// Associated type with trait bound

#[derive(Clone, Copy)]
struct S;

#[derive(Clone)]
struct CloneMe;

trait Foo3 {
    type AssocBounded: Clone;
    fn clone_assoc(&self, a: Self::AssocBounded) -> Self::AssocBounded;
}

impl Foo3 for S {
    type AssocBounded = CloneMe;
    fn clone_assoc(&self, a: Self::AssocBounded) -> Self::AssocBounded {
        a.clone()
    }
}

const ARG: i32 = 1;
fn f(arg: i32) {
    let s = S;
    let c = CloneMe;
    let c2 = s.clone_assoc(c);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
