// Method call via `Deref::deref`
use std::ops::Deref;

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
fn main() {
   println!("{:?}", f(ARG));
}
