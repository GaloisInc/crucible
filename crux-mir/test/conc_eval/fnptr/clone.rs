// A regression test for #1645. This ensures that crucible-mir supports
// translating a call to clone() on a FnDef, which requires a `clone` shim.

// Guard the call to clone() behind an intermediate function to reduce the
// likelihood that rustc optimizes away the call to clone().
#[inline(never)]
fn my_clone<T: Clone>(x: &T) -> T {
    x.clone()
}

pub fn f(x: i32) -> i32 {
    x
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> i32 {
    my_clone(&f)(42)
}

pub fn main() {
    println!("{:?}", crux_test());
}
