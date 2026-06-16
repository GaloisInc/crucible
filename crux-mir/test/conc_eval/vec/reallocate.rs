#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let orig_capacity = 1;
    let mut v = Vec::with_capacity(orig_capacity);
    while v.len() < v.capacity() {
        v.push(0);
    }
    v.push(1);
    assert_ne!(v.capacity(), orig_capacity);
    (v[0], *v.last().unwrap())
}

pub fn main() {
    println!("{:?}", crux_test());
}
