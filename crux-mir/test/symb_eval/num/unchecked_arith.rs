#![feature(unchecked_shifts)]

#[crux::test]
fn add_test() -> u8 {
    unsafe { 100u8.unchecked_add(200) }
}

#[crux::test]
fn sub_test() -> u8 {
    unsafe { 100u8.unchecked_sub(200) }
}

#[crux::test]
fn mul_test() -> u8 {
    unsafe { 100u8.unchecked_mul(200) }
}

#[crux::test]
fn shl_test() -> u8 {
    unsafe { 100u8.unchecked_shl(200) }
}

#[crux::test]
fn shr_test() -> u8 {
    unsafe { 100u8.unchecked_shr(200) }
}

pub fn main() {
    println!("{:?} {:?} {:?} {:?} {:?}",
             add_test(), sub_test(), mul_test(), shl_test(), shr_test());
}
