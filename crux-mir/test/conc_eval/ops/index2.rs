// Method call via `Index::index`
use std::ops::Index;

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
fn main() {
   println!("{:?}", f(ARG));
}
