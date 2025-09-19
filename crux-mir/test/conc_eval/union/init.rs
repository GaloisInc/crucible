union U {
    x: u16,
    y: [u8; 2],
}

#[cfg_attr(crux, crux::test)]
fn foo() -> u16 {
    let x: u16 = 0x1234;
    let u: U = U { x };
    x
}

fn main() {
    println!("{}", foo());
}
