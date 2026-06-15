#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut x = 0;
    for &() in [(), (), ()].as_slice() {
        x += 1;
    }
    x
}

pub fn main() {
    println!("{:?}", crux_test());
}
