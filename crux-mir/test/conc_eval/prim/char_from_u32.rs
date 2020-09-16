use std::char;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> char {
    unsafe { char::from_u32_unchecked(0x41) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
