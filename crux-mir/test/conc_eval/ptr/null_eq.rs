use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = 1;
    let px = &x as *const i32;
    assert!(px != ptr::null());
    assert!(ptr::null::<i32>() == ptr::null());
    assert!(ptr::null_mut::<i32>() as *const _ == ptr::null());
    // Note we don't check `px == px`, since that currently returns false under crux-mir.
    unsafe { *px }
}

pub fn main() {
    println!("{:?}", crux_test());
}
