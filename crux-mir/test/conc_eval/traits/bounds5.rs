// impl where impl'ed trait and bound both have associated types
#![cfg_attr(not(with_main), no_std)]

trait Foo {
    fn method(&self) -> i32;
    fn static_method() -> i32;
    fn default_method(&self) -> i32 {
        self.method() + Self::static_method()
    }
}

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

impl Foo for S {
    fn method(&self) -> i32 { 1 }
    fn static_method() -> i32 { 2 }
}

impl Foo2 for S {
    type Assoc = i32;

    fn take_assoc(&self, a: Self::Assoc) -> i32 { a }
    fn give_assoc(&self, a: i32) -> Self::Assoc { a }
}


impl<T: Foo2> Foo2 for Option<T> {
    type Assoc = i32;
    fn take_assoc(&self, a: Self::Assoc) -> i32 { a }
    fn give_assoc(&self, a: i32) -> Self::Assoc {
        if let Some(ref x) = *self {
            x.take_assoc(x.give_assoc(a))
        } else {
            a
        }
    }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let some_s = Some(S);
    assert!(some_s.take_assoc(1) == 1);
    assert!(some_s.give_assoc(1) == 1);
    assert!(some_s.default_with_assoc(1) == 1);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
