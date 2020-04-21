
#[cfg_attr(crux, crux_test)]
fn crux_test() -> bool {
    let mut s = String::new();
    s.push('a');
    s.push('β');
    s.push('c');
    &s == "aβc"
}

pub fn main() {
    println!("{:?}", crux_test());
}
