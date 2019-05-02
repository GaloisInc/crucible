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
fn main() {
    unsafe {
        println!("{:?}", f(ARG));
    }
}
