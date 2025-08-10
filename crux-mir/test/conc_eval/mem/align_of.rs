struct Thing {
    x: u32,
    y: i128,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [usize; 4] {
    [align_of::<u8>(), align_of::<(i16, i32)>(), align_of::<[u64; 3]>(), align_of::<Thing>()]
}

pub fn main() {
    println!("{:?}", crux_test());
}
