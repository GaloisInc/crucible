
#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let dest: &[u8] = &[];
    dest.len()
}

pub fn main() {
    println!("{:?}", crux_test());
}
