extern crate dlmalloc;
extern crate rand;

use dlmalloc::Dlmalloc;
use rand::Rng;
use std::cmp;

#[test]
fn smoke() {
    let mut a = Dlmalloc::new();
    unsafe {
        let ptr = a.malloc(1, 1);
        assert!(!ptr.is_null());
        *ptr = 9;
        assert_eq!(*ptr, 9);
        a.free(ptr, 1, 1);

        let ptr = a.malloc(1, 1);
        assert!(!ptr.is_null());
        *ptr = 10;
        assert_eq!(*ptr, 10);
        a.free(ptr, 1, 1);
    }
}

#[test]
fn stress() {
    let mut a = Dlmalloc::new();
    let mut rng = rand::thread_rng();
    let mut ptrs = Vec::new();
    let max = if cfg!(test_lots) { 1_000_000 } else { 1_000 };
    unsafe {
        for _ in 0..max {
            let free =
                ptrs.len() > 0 && ((ptrs.len() < 10_000 && rng.gen_weighted_bool(3)) || rng.gen());
            if free {
                let idx = rng.gen_range(0, ptrs.len());
                let (ptr, size, align) = ptrs.swap_remove(idx);
                a.free(ptr, size, align);
                continue;
            }

            if ptrs.len() > 0 && rng.gen_weighted_bool(100) {
                let idx = rng.gen_range(0, ptrs.len());
                let (ptr, size, align) = ptrs.swap_remove(idx);
                let new_size = if rng.gen() {
                    rng.gen_range(size, size * 2)
                } else if size > 10 {
                    rng.gen_range(size / 2, size)
                } else {
                    continue;
                };
                let mut tmp = Vec::new();
                for i in 0..cmp::min(size, new_size) {
                    tmp.push(*ptr.offset(i as isize));
                }
                let ptr = a.realloc(ptr, size, align, new_size);
                assert!(!ptr.is_null());
                for (i, byte) in tmp.iter().enumerate() {
                    assert_eq!(*byte, *ptr.offset(i as isize));
                }
                ptrs.push((ptr, new_size, align));
            }

            let size = if rng.gen() {
                rng.gen_range(1, 128)
            } else {
                rng.gen_range(1, 128 * 1024)
            };
            let align = if rng.gen_weighted_bool(10) {
                1 << rng.gen_range(3, 8)
            } else {
                8
            };

            let zero = rng.gen_weighted_bool(50);
            let ptr = if zero {
                a.calloc(size, align)
            } else {
                a.malloc(size, align)
            };
            for i in 0..size {
                if zero {
                    assert_eq!(*ptr.offset(i as isize), 0);
                }
                *ptr.offset(i as isize) = 0xce;
            }
            ptrs.push((ptr, size, align));
        }
    }
}
