#![cfg_attr(not(with_main), no_std)]
// impl with multiple trait bounds on type parameter

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


impl<T: Foo + Clone> Foo for Option<T> {
    fn method(&self) -> i32 {
        if let Some(ref x) = *self {
            x.clone().method()
        } else {
            0
        }
    }
    fn static_method() -> i32 { T::static_method() }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let some_s = Some(S);
    assert!(some_s.method() == 1);
    assert!(<Option<S>>::static_method() == 2);
    assert!(some_s.default_method() == 3);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
