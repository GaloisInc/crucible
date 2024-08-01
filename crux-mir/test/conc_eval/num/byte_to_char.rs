pub fn b() -> u8 {
    97
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> char {
    b() as char
}

pub fn main() { println!("{:?}", crux_test()); }
