//! This exercises `RawVec`'s `[u8; N]` allocation behavior, which had precisely
//! the same `*const [u8; N]` to `*const u8` casting issue as `TypedAllocator`,
//! as described and tested against in `u8_array_push.rs` in this directory. See
//! https://github.com/GaloisInc/mir-json/pull/150.

#[cfg_attr(crux, crux::test)]
fn test() -> [u8; 4] {
    let mut v: Vec<[u8; 4]> = vec![[1, 2, 3, 4]];
    v[0]
}

fn main() {
    println!("{:?}", test());
}
