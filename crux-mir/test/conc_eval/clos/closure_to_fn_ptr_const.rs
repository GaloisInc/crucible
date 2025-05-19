static F: fn() -> i32 = const { || 123 };

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let g: fn() -> i32 = const { || 123 };
    F() + g()
}

pub fn main() {
    println!("{:?}", crux_test());
}
