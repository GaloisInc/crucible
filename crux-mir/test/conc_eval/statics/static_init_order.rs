// A test case which ensures that the static initializer for `Y` is translated
// after the constant allocation `{{alloc}}[0]` that it depends on. This is one
// very specific instance of #1108, which is a more general issue in how
// crucible-mir translates static items.

const X: &[u64] = &[42];
pub static Y: u64 = X[0];

pub fn f() -> &'static u64 {
    &Y
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u64 {
    *f()
}

pub fn main() {
    println!("{:?}", crux_test());
}
