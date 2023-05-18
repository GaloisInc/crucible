#![allow(arithmetic_overflow)]

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u8 {
    let x = 200;
    100 + x
}

pub fn main() {
    println!("{:?}", crux_test());
}
