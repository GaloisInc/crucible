#![cfg_attr(not(with_main), no_std)]
trait Foo2 {
    type Assoc;
    fn take_assoc(&self, a: Self::Assoc) -> i32;
    fn give_assoc(&self, a: i32) -> Self::Assoc;
    fn default_with_assoc(&self, a: i32) -> i32 {
        self.take_assoc(self.give_assoc(a))
    }
}

#[derive(Clone, Copy)]
struct S;

impl Foo2 for S {
    type Assoc = i32;

    fn take_assoc(&self, a: Self::Assoc) -> i32 { a }
    fn give_assoc(&self, a: i32) -> Self::Assoc { a }
}

const ARG: i32 = 1;
fn f(arg: i32) {
    let s = S;
    assert!(s.take_assoc(1) == 1);
    assert!(s.give_assoc(1) == 1);
    assert!(s.default_with_assoc(1) == 1);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> () { f(ARG) }
