// This test passes, despite initalizing a `U` with its `u16` field and reading
// from it with its `i16` field, because `u16` and `i16` share a Crucible
// representation.

union U {
    x: u16,
    y: i16,
}

#[cfg_attr(crux, crux::test)]
fn foo() -> i16 {
    let x: u16 = 0xffff;
    let u: U = U { x };

    let y = unsafe { u.y };
    assert!(y.is_negative());
    y
}

fn main() {
    println!("{:?}", foo());
}
