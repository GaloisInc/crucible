
#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let r = &&1;
    let r2 = *r;
    *r2
}

pub fn main() {
    println!("{:?}", crux_test());
}
