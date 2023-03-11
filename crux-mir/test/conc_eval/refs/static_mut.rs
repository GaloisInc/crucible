
static mut X: usize = 1;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> usize {
    let mut x = unsafe { &mut X };
    *x += 1;
    *x
}

pub fn main() {
    println!("{:?}", crux_test());
}
