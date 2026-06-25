// A regression test for #1855, which ensures that the `std::hint::black_box`
// and `std::intrinsics::black_box` functions are supported.
#![feature(core_intrinsics)]

fn f(x: bool) {
    assert_eq!(std::hint::black_box(42u8), 42u8);
    assert_eq!(std::intrinsics::black_box(42u16), 42u16);
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() {
    f(false)
}

pub fn main() {
    println!("{:?}", crux_test());
}
