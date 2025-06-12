use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x = 12;
    let y = &x as *const i32;
    unsafe {
        assert!(std::ptr::read_volatile(y) == 12);
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
