#![feature(unsize)]
#![feature(coerce_unsized)]
use std::marker::Unsize;
use std::ops::CoerceUnsized;
use std::ptr;

struct MyPtr<T: ?Sized>(*const T);
impl<T: Unsize<U> + ?Sized, U: ?Sized> CoerceUnsized<MyPtr<U>> for MyPtr<T> {}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let a = [1, 2];
    let arr_ptr = MyPtr(&a as *const [i32; 2]);
    // This cast requires CoerceUnsized
    let slice_ptr = arr_ptr as MyPtr<[i32]>;
    let ptr = slice_ptr.0 as *const i32;
    unsafe { (*ptr, *ptr.offset(1)) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
