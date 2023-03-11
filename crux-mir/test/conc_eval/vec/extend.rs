use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, i32) {
    let mut v = Vec::new();
    v.push(1);
    v.push(2);
    // `filter` iterators don't implement `TrustedLen`.  `TrustedLen` iterators take a different
    // code path, which is tested in `extend_trusted_len.rs`.
    v.extend([10, 11].iter().cloned().filter(|_| true));
    (v[0], v[2])
}

pub fn main() {
    println!("{:?}", crux_test());
}
