
pub fn call_it<F: FnMut(i32) -> i32>(f: F) -> i32 {
    let mut f = f;
    f(1)
}

#[crux_test]
pub fn f() -> i32 {
    let x = 1;
    let mut z = 0;
    let a = call_it(|y| { z += 1; x + y + z });
    let b = call_it(&mut |y| { z += 1; x + y + z });
    a + b
}

#[cfg(with_main)] pub fn main() { println!("{:?}", f()); }
