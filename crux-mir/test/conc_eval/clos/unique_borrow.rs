
fn call_it<F: FnMut() -> i32>(mut f: F) -> i32 {
    f() + f()
}

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let mut x = 0;
    let y: &mut i32 = &mut x;
    call_it(|| {
        *y += 1;
        *y
    })
}

pub fn main() {
    println!("{:?}", crux_test());
}
