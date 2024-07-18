type T = u64;
const COUNT: usize = 16;

pub fn output_array(src: &[T; COUNT], dst: *mut T) {
    unsafe {
        std::ptr::copy(src as *const T, dst, COUNT);
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> T {
    let src: &[T; COUNT] = &[42; COUNT];
    let dst: &mut [T; COUNT] = &mut [0; COUNT];
    output_array(src, dst as *mut T);
    dst[0]
}

pub fn main() {
    println!("{:?}", crux_test());
}
