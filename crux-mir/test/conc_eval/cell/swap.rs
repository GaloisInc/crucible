use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let c1 = Cell::new(5i32);
    let c2 = Cell::new(10i32);
    c1.swap(&c2);
    assert_eq!(10, c1.get());
    assert_eq!(5, c2.get());
}

pub fn main() {
    println!("{:?}", crux_test());
}
