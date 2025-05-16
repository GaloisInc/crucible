use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut x = 0;
    let cell = Cell::from_mut(&mut x);
    cell.set(3);
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
