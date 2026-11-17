#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> (u32, i32, u8, i8) {
    let a: char = 'a';
    let f: char = '\u{FF}';
    (a as u32, a as i32, f as u8, f as i8)
}

pub fn main() {
    println!("{:?}", crux_test());
}
