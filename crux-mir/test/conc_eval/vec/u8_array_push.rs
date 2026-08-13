//! This exercises `TypedAllocator`'s `[u8; N]` allocation behavior, which
//! involves a `*const [u8; N]` to `*const u8` pointer cast.

#[cfg_attr(crux, crux::test)]
fn test() -> [u8; 4] {
    let mut v: Vec<[u8; 4]> = Vec::new();
    let a: [u8; 4] = [1, 2, 3, 4];
    v.push(a);
    v[0]
}

fn main() {
    println!("{:?}", test());
}
