#![feature(signed_bigint_helpers)]

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (u8, i8) {
    i8::MAX.carrying_mul(i8::MAX, i8::MAX)
}

pub fn main() {
    println!("{:?}", crux_test());
}
