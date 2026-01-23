#[repr(transparent)]
struct Wrapper {
    array: [i32; 5],
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let array = [1, 2, 3, 4, 5];
    let wrapper = Wrapper { array };
    let ptr_to_first = &raw const wrapper as *const i32;
    unsafe { *ptr_to_first }
}

pub fn main() {
    println!("{:?}", crux_test());
}
