//! This test checks that we can correctly write `MirAggregate`s to a reference
//! with an `Empty_RefPath` that already contains a larger aggregate.

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [[u8; 1]; 2] {
    let xs = [42u8; 1];
    let mut ys = [xs; 2];
    for y in ys.iter_mut() {
        *y = [0u8; 1];
    }
    assert_eq!(ys[0], [0]);
    assert_eq!(ys[1], [0]);
    ys
}

pub fn main() {
    println!("{:?}", crux_test())
}
