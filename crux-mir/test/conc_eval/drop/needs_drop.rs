use std::mem::needs_drop;

struct Foo(u32);

impl Drop for Foo {
    fn drop(&mut self) {}
}

struct Bar(u32);

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    assert!(needs_drop::<Foo>());
    assert!(!needs_drop::<Bar>());
    assert!(!needs_drop::<u32>());
}

fn main() {
    println!("{:?}", crux_test());
}
