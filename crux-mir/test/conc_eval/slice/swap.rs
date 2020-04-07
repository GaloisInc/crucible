use std::ptr;

#[crux_test]
pub fn f() -> i32 {
    let mut v = [1, 2];
    unsafe {
        // This mimics the swap operation used in the normal slice::sort implementation.  (But note
        // the real version uses a `Drop` impl for the final copy, which we don't support.)
        let tmp = ptr::read(&v[0]);
        ptr::copy_nonoverlapping(&v[1], &mut v[0], 1);
        ptr::copy_nonoverlapping(&tmp, &mut v[1], 1);
    }
    v[0] * 1000 + v[1]
}


fn main() { println!("{:?}", f()); }
