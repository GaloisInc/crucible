// A regression test for #1733. This tests the constant translation machinery
// on slice raw pointers (namely, the Y1 and Y2 constants).

const X1: &[u8] = &[1, 2];
const Y1: *const [u8] = X1 as _;

const X2: &str = &"hello";
const Y2: *const str = X2 as _;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> (usize, usize) {
    let y1_len = Y1.len();
    let y2_u8: *const u8 = Y2 as _;
    let y2_u8_slice: &[u8] = unsafe { std::slice::from_raw_parts(y2_u8, X2.len()) };
    (Y1.len(), y2_u8_slice.len())
}

fn main() {
    println!("{:?}", crux_test());
}
