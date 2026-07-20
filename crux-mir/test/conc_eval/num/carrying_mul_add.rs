#[cfg_attr(crux, crux::test)]
fn crux_test() -> (u8, u8) {
    let (x1, x0) = (0x01, 0x23);
    let y = 0x05;
    let (z1, z0) = (0x01, 0x80);
    // Bignum arithmetic: r = x * y + z
    let (r0, c0) = u8::carrying_mul_add(x0, y, 0, z0);
    let (r1, _c1) = u8::carrying_mul_add(x1, y, c0, z1);
    (r1, r0)
}

pub fn main() {
    println!("{:?}", crux_test());
}
