// FAIL: writing a non-active union field

union U {
    x: u16,
    y: [u8; 2],
}

#[cfg_attr(crux, crux::test)]
fn foo() -> u16 {
    let mut u: U = U { x: 0xffff };
    let x: u16 = 0x1234;
    let y: [u8; 2] = x.to_ne_bytes();

    u.y = y;
    let x1 = unsafe { u.x };
    assert_eq!(x, x1);
    x1
}

fn main() {
    println!("{}", foo());
}
