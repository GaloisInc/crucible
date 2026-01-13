#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    let a: [u32; 5] = [1, 2, 3, 4, 5];
    let b: &[u32] = &a;
    let c: *const [u32] = b;
    let d: *const u32 = c as *const u32;
    let e: *const u8 = d as *const u8;
    let f: *const u8 = unsafe { e.offset(4) };
    let g: *const u32 = f as *const u32;
    unsafe { *g }
}

fn main() {
    println!("{}", crux_test());
}
