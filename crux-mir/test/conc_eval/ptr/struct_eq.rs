use std::ptr;

struct Foo {
    x: i32,
    y: i32,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let a = Foo { x: 1, y: 1 };
    let b = Foo { x: 1, y: 1 };
    assert!(&a.x as *const _ == &a.x as *const _);
    assert!(&a.x as *const _ != &a.y as *const _);
    assert!(&a.x as *const _ != &b.x as *const _);
}

pub fn main() {
    println!("{:?}", crux_test());
}
