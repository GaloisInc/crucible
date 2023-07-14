
#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let dest: &mut [u8] = &mut [];
    dest.len()
}

pub fn main() {
    println!("{:?}", crux_test());
}
