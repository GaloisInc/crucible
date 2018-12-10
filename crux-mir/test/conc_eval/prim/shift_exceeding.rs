// FAIL: Should panic, but doesn't
#[allow(exceeding_bitshifts)]
fn f(x: i64) -> i64 {
    x << 64i64
}

const ARG: i64 = 1;

#[cfg(with_main)]
fn main() {
    use std::panic;
    let result = panic::catch_unwind(|| {
        f(ARG)
    });
    match result {
        Ok(r) => println!("{:?}", r),
        Err(_) => println!("<<PANIC>>"),
    };
}
