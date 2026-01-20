use std::sync::atomic::{AtomicPtr, Ordering};

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let ptr = &mut 5;
    let some_ptr = AtomicPtr::new(ptr);
    let other_ptr = &mut 10;
    let value = some_ptr.swap(other_ptr, Ordering::Relaxed);
    let other_value = some_ptr.load(Ordering::Relaxed);
    assert_eq!(unsafe { *value }, 5);
    assert_eq!(unsafe { *other_value }, 10);

    let another_ptr = &mut 15;
    some_ptr.store(another_ptr, Ordering::Relaxed);
    let another_value = some_ptr.load(Ordering::Relaxed);
    assert_eq!(unsafe { *another_value }, 15);
}

pub fn main() {
    println!("{:?}", crux_test());
}
