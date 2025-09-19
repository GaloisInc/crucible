// FAIL: reading a non-active union field

union U {
    x: u16,
    y: [u8; 2],
}

#[cfg_attr(crux, crux::test)]
fn foo() -> [u8; 2] {
    let x: u16 = 0x1234;
    let u: U = U { x };

    let y = unsafe { u.y };
    assert_eq!(y, x.to_ne_bytes());
    y
}

fn main() {
    println!("{:?}", foo());
}
