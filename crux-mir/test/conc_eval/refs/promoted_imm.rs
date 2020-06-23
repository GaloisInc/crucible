
#[cfg_attr(crux, crux_test)]
fn crux_test() -> usize {
    let dest: &[u8] = &[];
    dest.len()
}

pub fn main() {
    println!("{:?}", crux_test());
}
