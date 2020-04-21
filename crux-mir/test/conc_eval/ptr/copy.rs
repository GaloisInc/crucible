use std::ptr;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> [i32; 6] {
    let a = [1, 2, 3];
    let mut b = [0; 6];
    unsafe {
        ptr::copy(&a[0], &mut b[0], 3);
        ptr::copy_nonoverlapping(&b[0], &mut b[3], 3);
    }
    b
}

pub fn main() {
    println!("{:?}", crux_test());
}
