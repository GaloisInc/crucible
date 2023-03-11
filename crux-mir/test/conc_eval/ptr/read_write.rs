use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [i32; 3] {
    let mut a = [1, 2, 3];
    unsafe {
        let p0 = &mut a[0] as *mut _;
        let p1 = &mut a[1] as *mut _;
        let p2 = &mut a[2] as *mut _;
        let x = ptr::read(p0);
        ptr::write(p1, x);
        ptr::swap(p1, p2);
    }
    a
}

pub fn main() {
    println!("{:?}", crux_test());
}
