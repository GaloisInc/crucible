use std::ptr;

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    let d = ptr::NonNull::<i32>::dangling().as_ptr();
    assert!(d != ptr::null_mut());
    assert!(d == d);
}

pub fn main() {
    println!("{:?}", crux_test());
}
