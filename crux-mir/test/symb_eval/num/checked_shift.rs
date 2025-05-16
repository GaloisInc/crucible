#![allow(arithmetic_overflow)]

#[crux::test]
fn crux_test() -> i64 {
    let x = 1;
    x << 64i64
}

pub fn main() {
    println!("{:?}", crux_test());
}
