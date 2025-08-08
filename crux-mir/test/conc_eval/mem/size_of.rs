struct Thing {
    x: u32,
    y: i128,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [usize; 4] {
    [size_of::<u8>(), size_of::<(i16, i32)>(), size_of::<[u64; 3]>(), size_of::<Thing>()]
}

pub fn main() {
    println!("{:?}", crux_test());
}
