#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    let x = Box::new(123_i32);
    let mut y = x.clone();
    assert!(*x == *y);
    *y = 456;
    assert!(*x == 123);
    assert!(*y == 456);
}

pub fn main() {
    println!("{:?}", crux_test())
}
