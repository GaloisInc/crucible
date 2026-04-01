//! A regression test for #1793. `crux-mir` should report an error message at
//! the call to `override_`, reporting that the overridden and overriding
//! functions have incompatible types.

extern crate crucible;
use crucible::{crucible_assert, override_, Symbolic};

fn f(x: &u16, y: &u16) -> u16 {
    unimplemented!()
}

fn g(x: &u8, y: &u16) -> u16 {
    (*x as u16).wrapping_add(*y)
}

#[crux::test]
fn test() {
    override_(f, g);
    let x = u16::symbolic("x");
    let y = u16::symbolic("y");
    let actual = f(&x, &y);
    let expected = x.wrapping_add(y);
    crucible_assert!(actual == expected);
}
