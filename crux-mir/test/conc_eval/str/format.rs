
#[cfg_attr(crux, crux_test)]
fn crux_test() -> bool {
    let s = format!("a{}c", 'β');
    &s == "aβc"
}

pub fn main() {
    println!("{:?}", crux_test());
}
