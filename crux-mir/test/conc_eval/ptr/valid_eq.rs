use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x = 1;
    let y = 2;
    assert!(&x as *const _ == &x as *const _);
    assert!(&x as *const _ != &y as *const _);
}

pub fn main() {
    println!("{:?}", crux_test());
}
