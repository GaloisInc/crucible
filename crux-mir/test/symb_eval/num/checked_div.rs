#[inline(never)]
fn div_signed(x: i8, y: i8) -> i8 {
    x / y
}

#[inline(never)]
fn div_unsigned(x: u8, y: u8) -> u8 {
    x / y
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> u8 {
    let a: i8 = div_signed(1, 1);
    let b: i8 = div_signed(-128, -1);   // Should fail
    let c: i8 = div_signed(-128, -2);
    let d: i8 = div_signed(-127, -1);
    let e: i8 = div_signed(-1, 0);      // Should fail

    let f: u8 = div_unsigned(1, 1);
    let g: u8 = div_unsigned(1, 0);     // Should fail

    (a + b + c + d + e) as u8 + (f + g)
}

pub fn main() {
    println!("{:?}", crux_test());
}
