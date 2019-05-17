// Method call via `IndexMut::index_mut`
use std::ops::{Index, IndexMut};

struct MyPtr<T>(T);

impl<T> Index<usize> for MyPtr<T> {
    type Output = T;
    fn index(&self, idx: usize) -> &T {
        &self.0
    }
}

impl<T> IndexMut<usize> for MyPtr<T> {
    fn index_mut(&mut self, idx: usize) -> &mut T {
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
    assert!(p[123].bar());
}

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
