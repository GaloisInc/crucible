pub fn foo(f: &mut dyn FnMut(i16, i32) -> i32) -> i32 {
    f(27, 42)
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    foo(&mut |x, y| x as i32 + y as i32)
}

pub fn main() {
    println!("{:?}", crux_test());
}
