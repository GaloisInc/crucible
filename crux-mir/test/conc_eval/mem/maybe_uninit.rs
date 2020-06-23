use std::mem::MaybeUninit;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut i = MaybeUninit::uninit();
    unsafe {
        *i.as_mut_ptr() = 1;
        i.assume_init()
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
