// FAIL: error translating Deref impls
// Method call via `DerefMut::deref_mut`
use std::ops::{Deref, DerefMut};

struct MyPtr<T>(T);

impl<T> Deref for MyPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}

impl<T> DerefMut for MyPtr<T> {
    fn deref_mut(&mut self) -> &mut T {
        &mut self.0
    }
}


struct S;

impl S {
    fn foo(&self) -> bool { true }
    fn bar(&mut self) -> bool { true }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let mut p = MyPtr(S);
    assert!(p.bar());
}

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
