use std::cell::Cell;
use std::sync::Arc;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let a = Arc::new(Cell::new(1));
    let b = a.clone();
    a.set(2);
    a.get() + b.get()
}

pub fn main() {
    println!("{:?}", crux_test());
}
