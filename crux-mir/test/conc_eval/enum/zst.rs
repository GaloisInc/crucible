#[derive(Debug)]
enum A {
    B,
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> A {
    let arr = [A::B];
    unsafe { std::ptr::read(&raw const arr[0]) }
}

pub fn main() {
    println!("{:?}", crux_test());
}
