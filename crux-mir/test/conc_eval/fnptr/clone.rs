// A regression test for #1645. This ensures that crucible-mir supports
// translating a call to clone() on a FnDef, which requires a `clone` shim.

pub fn dup<C: Clone>(x: C) -> (C, C) {
    (x.clone(), x)
}

pub fn f(x: i32) -> i32 {
    x
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> i32 {
    (dup(f).0)(42)
}

pub fn main() {
    println!("{:?}", crux_test());
}
