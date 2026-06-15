use std::cell::Cell;

thread_local! {
    static X: Cell<i32> = Cell::new(123);
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x = X.get();
    X.set(1);
    let y = X.get();
    x + y
}

pub fn main() {
    println!("{:?}", crux_test());
}
