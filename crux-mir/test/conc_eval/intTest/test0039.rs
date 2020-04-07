#![cfg_attr(not(with_main), no_std)]
#[no_mangle]
static mut X: i32 = 0;

#[inline(never)]
#[no_mangle]
pub unsafe fn ff(y: i32) -> i32 {
    X = X + 1;
    return X + y;
}

#[inline(never)]
#[no_mangle]
pub unsafe fn g(z: i32) -> i32 {
    X = X + 2;
    return X + z;
}

#[inline(never)]
#[no_mangle]
pub unsafe fn f(w: i32) -> i32 {
    return g(ff(w));
}


const ARG: i32 = 3;

#[cfg(with_main)]
pub fn main() {
    unsafe {
        println!("{:?}", f(ARG));
    }
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> i32 { unsafe { f(ARG) } }
