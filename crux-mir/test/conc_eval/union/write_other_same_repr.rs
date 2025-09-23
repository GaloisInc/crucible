// This test passes, despite initalizing a `U` with its `u16` field and writing
// to its `i16` field, because `u16` and `i16` share a Crucible representation.

union U {
    x: u16,
    y: i16,
}

#[cfg_attr(crux, crux::test)]
fn foo() -> u16 {
    let mut u: U = U { x: 0xffff };
    let x: u16 = 0x1234;
    let y: i16 = x as i16;

    u.y = y;
    let x1 = unsafe { u.x };
    assert_eq!(x, x1);
    x1
}

fn main() {
    println!("{}", foo());
}
