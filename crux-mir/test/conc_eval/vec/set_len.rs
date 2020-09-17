#[cfg_attr(crux, crux_test)]
fn crux_test() -> usize {
    let mut v = vec![1, 2, 3];
    unsafe { v.set_len(2); }
    (&v as &[i32]).len()
}

pub fn main() {
    println!("{:?}", crux_test());
}
