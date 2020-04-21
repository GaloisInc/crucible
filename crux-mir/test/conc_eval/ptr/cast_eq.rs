use std::ptr;

#[cfg_attr(crux, crux_test)]
fn crux_test() {
    let p1 = 1 as *const i32;
    let p1b = 1 as *const i32;
    let p2 = 2 as *const i32;
    assert!(p1 == p1b);
    assert!(p1 != p2);
    assert!(p2 == p2);
}

pub fn main() {
    println!("{:?}", crux_test());
}
