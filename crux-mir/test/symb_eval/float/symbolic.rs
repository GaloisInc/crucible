#![feature(f16)]
#![feature(f128)]

extern crate crucible;
use crucible::*;

macro_rules! symbolic_test {
    ($t:ty) => {
        {
            let x = <$t>::symbolic("x");
            crucible_assume!(!x.is_nan()); // NaN is not equal to itself
            crucible_assert!(x == x);
            x
        }
    };
}

#[crux::test]
fn f16_test() -> f16 {
    symbolic_test!(f16)
}

#[crux::test]
fn f32_test() -> f32 {
    symbolic_test!(f32)
}

#[crux::test]
fn f64_test() -> f64 {
    symbolic_test!(f64)
}

#[crux::test]
fn f128_test() -> f128 {
    symbolic_test!(f128)
}
