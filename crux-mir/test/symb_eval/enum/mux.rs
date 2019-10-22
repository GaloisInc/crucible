#![feature(custom_attribute)]
extern crate crucible;

struct S {
    val: u8,
}

fn f(x: bool) -> Option<S> {
    if x { Some(S { val: 1 }) } else { None }
}

#[crux_test]
fn test() {
    let x = crucible::crucible_u8("x") != 0;
    let y = f(x);
    if x { y.unwrap(); }
}
