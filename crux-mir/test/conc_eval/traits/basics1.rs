#![cfg_attr(not(with_main), no_std)]
trait Foo {
    fn method(&self) -> i32;
    fn static_method() -> i32;
    fn default_method(&self) -> i32 {
        self.method() + Self::static_method()
    }
}

#[derive(Clone, Copy)]
struct S;

impl Foo for S {
    fn method(&self) -> i32 { 1 }
    fn static_method() -> i32 { 2 }
}

const ARG: i32 = 1;
fn f(arg: i32) {
    let s = S;
    assert!(s.method() == 1);
    assert!(S::static_method() == 2);
    assert!(s.default_method() == 3);
}

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> () { f(ARG) }
