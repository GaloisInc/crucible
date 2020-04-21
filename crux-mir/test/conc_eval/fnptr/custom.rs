// FAIL: taking address of an overridden function
use core::mem;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut x = 1;
    let mut y = 2;
    let p: fn(&mut i32, &mut i32) = mem::swap;
    p(&mut x, &mut y);
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
