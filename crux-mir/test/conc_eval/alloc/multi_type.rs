// FAIL: reads/writes still expect a u64 target, even after cast
// Test storing values of different types in a single allocation.

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 {
    unsafe {
        let mut mem = Vec::<u64>::with_capacity(1);
        let ptr = mem.as_mut_ptr().cast::<u8>();
        let p1: *mut u8 = ptr;
        let p2: *mut u8 = ptr.add(1);
        let p3: *mut u32 = ptr.add(4).cast::<u32>();

        *p1 = 1;
        *p2 = 2;
        *p3 = 3;

        *p1 += 10;
        *p2 += 10;
        *p3 += 10;

        *p1 as u32 + *p2 as u32 + *p3
    }
}

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", crux_test());
}

