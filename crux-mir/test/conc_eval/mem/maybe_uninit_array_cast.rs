use std::mem::MaybeUninit;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> [i32; 2] {
    let mut i = MaybeUninit::uninit();
    unsafe {
        let ptr = i.as_mut_ptr() as *mut i32;
        *ptr = 1;
        *ptr.add(1) = 2;
        i.assume_init()
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
