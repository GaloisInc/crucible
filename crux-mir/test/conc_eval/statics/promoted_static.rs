
static X: &&i32 = &&1;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    **X
}

pub fn main() {
    println!("{:?}", crux_test());
}
