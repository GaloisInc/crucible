//! This exercises `TypedAllocator`'s `[u8; N]` allocation behavior, which once
//! involved a `*const [u8; N]` to `*const u8` pointer cast. Why is this cast
//! different from all other casts? `crucible-mir`'s custom array representation
//! means that it needs to insert an array-indexing operation in `*const [T; N]`
//! to `*const T` casts, even though in this particular case, that operation
//! results in a mistyped pointer, to which `[u8; N]`s cannot be written. See
//! https://github.com/GaloisInc/mir-json/pull/148.

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
