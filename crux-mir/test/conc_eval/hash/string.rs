use std::hash::{Hash, Hasher, DefaultHasher};

/// The siphash implementation in the standard library has different code paths for short inputs
/// that fit within an internal 8-byte buffer and longer inputs that exceed it.
const S1: &str = "long test string that will overflow the hasher buffer";
const S2: &str = "short";


#[cfg_attr(crux, crux::test)]
fn crux_test() -> (u64, u64) {
    let mut h1 = DefaultHasher::new();
    S1.hash(&mut h1);
    let x1 = h1.finish();

    let mut h2 = DefaultHasher::new();
    S2.hash(&mut h2);
    let x2 = h2.finish();

    (x1, x2)
}

pub fn main() {
    println!("{:?}", crux_test());
}
