#![cfg_attr(not(with_main), no_std)]
// Method call via `Index::index`
extern crate core;
use core::ops::Index;

struct MyPtr<T>(T);

impl<T> Index<usize> for MyPtr<T> {
    type Output = T;
    fn index(&self, idx: usize) -> &T {
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
    assert!(p[123].foo());
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
