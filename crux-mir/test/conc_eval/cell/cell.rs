use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = Cell::new(1);
    x.set(2);
    x.get()
}

pub fn main() {
    println!("{:?}", crux_test());
}
