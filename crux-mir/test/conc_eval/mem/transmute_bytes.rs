use std::mem::transmute;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> u8 {
    assert_eq!(unsafe { transmute::<u32, [u8; 4]>(0x01020304) }, [4, 3, 2, 1]);
    assert_eq!(unsafe { transmute::<[u8; 4], u32>([4, 3, 2, 1]) }, 0x01020304);
    1
}

pub fn main() {
    println!("{:?}", crux_test());
}
