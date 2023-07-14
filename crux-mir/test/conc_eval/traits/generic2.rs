// Trait with generic method
#![cfg_attr(not(with_main), no_std)]

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

fn call_generic<T: Foo5, U>(x: &Option<T>, y: U) -> U {
    x.generic(y)
}


const ARG: i32 = 1;
fn f(arg: i32) {
    let some_s = Some(S);
    assert!(call_generic(&some_s, 1) == 1);

}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
