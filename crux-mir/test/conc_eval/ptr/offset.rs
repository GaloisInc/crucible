use std::ptr;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let arr = [1, 2, 3];
    unsafe {
        let p = &arr[0] as *const i32;
        let p = p.offset(2);
        *p
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
