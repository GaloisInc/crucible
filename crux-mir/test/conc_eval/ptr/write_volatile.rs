use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let mut x = 0;
    let y = &mut x as *mut i32;
    let z = 12;
    unsafe {
        std::ptr::write_volatile(y, z);
        assert!(std::ptr::read_volatile(y) == 12);
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
