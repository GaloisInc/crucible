#![cfg_attr(not(with_main), no_std)]
#![cfg_attr(not(with_main), feature(custom_attribute))]
// Method call via `Deref::deref`
extern crate core;
use core::ops::Deref;

struct MyPtr<T>(T);

impl<T> Deref for MyPtr<T> {
    type Target = T;
    fn deref(&self) -> &T {
        &self.0
    }
}


struct S;

impl S {
    fn foo(&self) -> bool { true }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let p = MyPtr(S);
    assert!(p.foo());
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
