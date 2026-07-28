#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
enum E2 {
    A([u8; 2]),
}

#[repr(transparent)]
#[derive(Clone, Debug, Eq, PartialEq)]
enum E4 {
    A([u8; 4]),
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let e2s = [E2::A([1, 2]), E2::A([3, 4])];
    let _ = e2s.clone();
}

pub fn main() {
    println!("{:?}", crux_test());
}
