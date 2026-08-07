#![feature(f16)]
#![feature(f128)]

extern crate crucible;
use crucible::*;

fn symbolic_test<S: PartialEq + Symbolic>() -> S {
    let x = S::symbolic("x");
    crucible_assert!(x == x);
    x
}

#[crux::test]
fn f16_test() -> f16 {
    symbolic_test()
}

#[crux::test]
fn f32_test() -> f32 {
    symbolic_test()
}

#[crux::test]
fn f64_test() -> f64 {
    symbolic_test()
}

#[crux::test]
fn f128_test() -> f128 {
    symbolic_test()
}
