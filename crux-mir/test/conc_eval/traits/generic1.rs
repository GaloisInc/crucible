#![cfg_attr(not(with_main), no_std)]
// Trait with generic method

#[derive(Clone, Copy)]
struct S;

trait Foo5 {
    fn generic<T>(&self, x: T) -> T;
}

impl Foo5 for S {
    fn generic<T>(&self, x: T) -> T { x }
}

impl<T: Foo5> Foo5 for Option<T> {
    fn generic<U>(&self, y: U) -> U {
        if let Some(ref x) = *self {
            x.generic(y)
        } else {
            y
        }
    }
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let some_s = Some(S);
    assert!(some_s.generic(1) == 1);

}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
