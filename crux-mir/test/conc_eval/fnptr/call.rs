#![feature(custom_attribute)]

fn f(x: i32) -> i32 {
    x + 1
}

#[crux_test]
fn crux_test() -> i32 {
    let p: fn(i32) -> i32 = f;
    p(1)
}

pub fn main() {
    println!("{:?}", crux_test());
}
