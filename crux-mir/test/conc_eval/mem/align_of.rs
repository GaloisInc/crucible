#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    align_of::<u8>()
}

pub fn main() {
    println!("{}", crux_test());
}
