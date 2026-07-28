#[derive(Clone, Debug)]
#[repr(transparent)]
struct S([u8; 2]);

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> [S; 3] {
    let xs = [S([1, 2]), S([3, 4]), S([5, 6])];
    xs.clone()
}

pub fn main() {
    println!("{:?}", crux_test());
}
