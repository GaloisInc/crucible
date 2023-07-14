#![cfg_attr(not(with_main), no_std)]
// Associated type with trait + projection bounds

#[derive(Clone, Copy)]
struct S;

trait Foo2 {
    type Assoc;
    fn take_assoc(&self, a: Self::Assoc) -> i32;
    fn give_assoc(&self, a: i32) -> Self::Assoc;
    fn default_with_assoc(&self, a: i32) -> i32 {
        self.take_assoc(self.give_assoc(a))
    }
}

impl Foo2 for S {
    type Assoc = i32;

    fn take_assoc(&self, a: Self::Assoc) -> i32 { a }
    fn give_assoc(&self, a: i32) -> Self::Assoc { a }
}

trait Foo4 {
    type AssocFoo2: Foo2<Assoc = i32>;
    fn as_foo2(&self) -> Self::AssocFoo2;
}

impl Foo4 for S {
    type AssocFoo2 = S;
    fn as_foo2(&self) -> Self::AssocFoo2 {
        S
    }
}

const ARG: i32 = 1;
fn f(arg: i32) {
    let s = S;
    let s2 = s.as_foo2();
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
