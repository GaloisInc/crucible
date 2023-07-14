
#[cfg_attr(crux, crux::test)]
fn crux_test() -> bool {
    let s = format!("a{}c", 123);
    &s == "a123c"
}

pub fn main() {
    println!("{:?}", crux_test());
}
