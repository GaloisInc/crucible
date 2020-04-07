use std::ptr;

#[crux_test]
fn crux_test() -> i32 {
    let mut arr = [1, 2, 3];
    unsafe {
        let p = &mut arr[0] as *mut i32;
        let p = p.offset(2);
        *p
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
