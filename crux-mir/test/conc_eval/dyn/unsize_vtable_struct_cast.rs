#![feature(coerce_unsized)]
#![feature(unsize)]

use std::marker::Unsize;
use std::ops::{CoerceUnsized, Deref};

pub struct FakeArc<T: ?Sized>(*const T);

impl<T: ?Sized, U: ?Sized> CoerceUnsized<FakeArc<U>> for FakeArc<T>
where T: Unsize<U> {}

impl<T> FakeArc<T> {
    pub fn new(x: T) -> FakeArc<T> {
        FakeArc(Box::leak(Box::new(x)))
    }
}

impl<T: ?Sized> Deref for FakeArc<T> {
    type Target = T;
    fn deref(&self) -> &T {
        unsafe { &*self.0 }
    }
}

/////

trait Foo {
    fn bar(&self);
}

impl Foo for i32 {
    fn bar(&self) {}
}

/////

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let fa_i32: FakeArc<i32> = FakeArc::new(0);
    let fa_dyn_foo: FakeArc<dyn Foo> = fa_i32;
    fa_dyn_foo.bar();
}

pub fn main() {
    println!("{:?}", crux_test());
}
