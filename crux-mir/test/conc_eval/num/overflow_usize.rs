// Regression test for discrepancies in `usize` handling.

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [(usize, bool); 2] {
    [
        usize::MAX.overflowing_add(1),
        (isize::MAX as usize).overflowing_add(1),
    ]
}

pub fn main() {
    println!("{:?}", crux_test());
}
