#![feature(custom_attribute)]

#[crux_test]
fn crux_test() -> u8 {
    let x = 200;
    100 + x
}

pub fn main() {
    println!("{:?}", crux_test());
}
