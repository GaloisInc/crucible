
#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let r = &&1;
    **r
}

pub fn main() {
    println!("{:?}", crux_test());
}
