#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    size_of::<i32>()
}

pub fn main() {
    println!("{}", crux_test());
}
