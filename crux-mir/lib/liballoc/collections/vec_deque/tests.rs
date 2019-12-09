use super::*;

use ::test;

#[bench]
#[cfg(not(miri))] // Miri does not support benchmarks
fn bench_push_back_100(b: &mut test::Bencher) {
    let mut deq = VecDeque::with_capacity(101);
    b.iter(|| {
        for i in 0..100 {
            deq.push_back(i);
        }
        deq.head = 0;
        deq.tail = 0;
    })
}

#[bench]
#[cfg(not(miri))] // Miri does not support benchmarks
fn bench_push_front_100(b: &mut test::Bencher) {
    let mut deq = VecDeque::with_capacity(101);
    b.iter(|| {
        for i in 0..100 {
            deq.push_front(i);
        }
        deq.head = 0;
        deq.tail = 0;
    })
}

#[bench]
#[cfg(not(miri))] // Miri does not support benchmarks
fn bench_pop_back_100(b: &mut test::Bencher) {
    let mut deq = VecDeque::<i32>::with_capacity(101);

    b.iter(|| {
        deq.head = 100;
        deq.tail = 0;
        while !deq.is_empty() {
            test::black_box(deq.pop_back());
        }
    })
}

#[bench]
#[cfg(not(miri))] // Miri does not support benchmarks
fn bench_pop_front_100(b: &mut test::Bencher) {
    let mut deq = VecDeque::<i32>::with_capacity(101);

    b.iter(|| {
        deq.head = 100;
        deq.tail = 0;
        while !deq.is_empty() {
            test::black_box(deq.pop_front());
        }
    })
}

#[test]
fn test_swap_front_back_remove() {
    fn test(back: bool) {
        // This test checks that every single combination of tail position and length is tested.
        // Capacity 15 should be large enough to cover every case.
        let mut tester = VecDeque::with_capacity(15);
        let usable_cap = tester.capacity();
        let final_len = usable_cap / 2;

        for len in 0..final_len {
            let expected: VecDeque<_> = if back {
                (0..len).collect()
            } else {
                (0..len).rev().collect()
            };
            for tail_pos in 0..usable_cap {
                tester.tail = tail_pos;
                tester.head = tail_pos;
                if back {
                    for i in 0..len * 2 {
                        tester.push_front(i);
                    }
                    for i in 0..len {
                        assert_eq!(tester.swap_remove_back(i), Some(len * 2 - 1 - i));
                    }
                } else {
                    for i in 0..len * 2 {
                        tester.push_back(i);
                    }
                    for i in 0..len {
                        let idx = tester.len() - 1 - i;
                        assert_eq!(tester.swap_remove_front(idx), Some(len * 2 - 1 - i));
                    }
                }
                assert!(tester.tail < tester.cap());
                assert!(tester.head < tester.cap());
                assert_eq!(tester, expected);
            }
        }
    }
    test(true);
    test(false);
}

#[test]
fn test_insert() {
    // This test checks that every single combination of tail position, length, and
    // insertion position is tested. Capacity 15 should be large enough to cover every case.

    let mut tester = VecDeque::with_capacity(15);
    // can't guarantee we got 15, so have to get what we got.
    // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
    // this test isn't covering what it wants to
    let cap = tester.capacity();


    // len is the length *after* insertion
    for len in 1..cap {
        // 0, 1, 2, .., len - 1
        let expected = (0..).take(len).collect::<VecDeque<_>>();
        for tail_pos in 0..cap {
            for to_insert in 0..len {
                tester.tail = tail_pos;
                tester.head = tail_pos;
                for i in 0..len {
                    if i != to_insert {
                        tester.push_back(i);
                    }
                }
                tester.insert(to_insert, to_insert);
                assert!(tester.tail < tester.cap());
                assert!(tester.head < tester.cap());
                assert_eq!(tester, expected);
            }
        }
    }
}

#[test]
fn test_remove() {
    // This test checks that every single combination of tail position, length, and
    // removal position is tested. Capacity 15 should be large enough to cover every case.

    let mut tester = VecDeque::with_capacity(15);
    // can't guarantee we got 15, so have to get what we got.
    // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
    // this test isn't covering what it wants to
    let cap = tester.capacity();

    // len is the length *after* removal
    for len in 0..cap - 1 {
        // 0, 1, 2, .., len - 1
        let expected = (0..).take(len).collect::<VecDeque<_>>();
        for tail_pos in 0..cap {
            for to_remove in 0..=len {
                tester.tail = tail_pos;
                tester.head = tail_pos;
                for i in 0..len {
                    if i == to_remove {
                        tester.push_back(1234);
                    }
                    tester.push_back(i);
                }
                if to_remove == len {
                    tester.push_back(1234);
                }
                tester.remove(to_remove);
                assert!(tester.tail < tester.cap());
                assert!(tester.head < tester.cap());
                assert_eq!(tester, expected);
            }
        }
    }
}

#[test]
fn test_drain() {
    let mut tester: VecDeque<usize> = VecDeque::with_capacity(7);

    let cap = tester.capacity();
    for len in 0..=cap {
        for tail in 0..=cap {
            for drain_start in 0..=len {
                for drain_end in drain_start..=len {
                    tester.tail = tail;
                    tester.head = tail;
                    for i in 0..len {
                        tester.push_back(i);
                    }

                    // Check that we drain the correct values
                    let drained: VecDeque<_> = tester.drain(drain_start..drain_end).collect();
                    let drained_expected: VecDeque<_> = (drain_start..drain_end).collect();
                    assert_eq!(drained, drained_expected);

                    // We shouldn't have changed the capacity or made the
                    // head or tail out of bounds
                    assert_eq!(tester.capacity(), cap);
                    assert!(tester.tail < tester.cap());
                    assert!(tester.head < tester.cap());

                    // We should see the correct values in the VecDeque
                    let expected: VecDeque<_> = (0..drain_start)
                        .chain(drain_end..len)
                        .collect();
                    assert_eq!(expected, tester);
                }
            }
        }
    }
}

#[test]
fn test_shrink_to_fit() {
    // This test checks that every single combination of head and tail position,
    // is tested. Capacity 15 should be large enough to cover every case.

    let mut tester = VecDeque::with_capacity(15);
    // can't guarantee we got 15, so have to get what we got.
    // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
    // this test isn't covering what it wants to
    let cap = tester.capacity();
    tester.reserve(63);
    let max_cap = tester.capacity();

    for len in 0..=cap {
        // 0, 1, 2, .., len - 1
        let expected = (0..).take(len).collect::<VecDeque<_>>();
        for tail_pos in 0..=max_cap {
            tester.tail = tail_pos;
            tester.head = tail_pos;
            tester.reserve(63);
            for i in 0..len {
                tester.push_back(i);
            }
            tester.shrink_to_fit();
            assert!(tester.capacity() <= cap);
            assert!(tester.tail < tester.cap());
            assert!(tester.head < tester.cap());
            assert_eq!(tester, expected);
        }
    }
}

#[test]
fn test_split_off() {
    // This test checks that every single combination of tail position, length, and
    // split position is tested. Capacity 15 should be large enough to cover every case.

    let mut tester = VecDeque::with_capacity(15);
    // can't guarantee we got 15, so have to get what we got.
    // 15 would be great, but we will definitely get 2^k - 1, for k >= 4, or else
    // this test isn't covering what it wants to
    let cap = tester.capacity();

    // len is the length *before* splitting
    for len in 0..cap {
        // index to split at
        for at in 0..=len {
            // 0, 1, 2, .., at - 1 (may be empty)
            let expected_self = (0..).take(at).collect::<VecDeque<_>>();
            // at, at + 1, .., len - 1 (may be empty)
            let expected_other = (at..).take(len - at).collect::<VecDeque<_>>();

            for tail_pos in 0..cap {
                tester.tail = tail_pos;
                tester.head = tail_pos;
                for i in 0..len {
                    tester.push_back(i);
                }
                let result = tester.split_off(at);
                assert!(tester.tail < tester.cap());
                assert!(tester.head < tester.cap());
                assert!(result.tail < result.cap());
                assert!(result.head < result.cap());
                assert_eq!(tester, expected_self);
                assert_eq!(result, expected_other);
            }
        }
    }
}

#[test]
fn test_from_vec() {
    use crate::vec::Vec;
    for cap in 0..35 {
        for len in 0..=cap {
            let mut vec = Vec::with_capacity(cap);
            vec.extend(0..len);

            let vd = VecDeque::from(vec.clone());
            assert!(vd.cap().is_power_of_two());
            assert_eq!(vd.len(), vec.len());
            assert!(vd.into_iter().eq(vec));
        }
    }
}

#[test]
fn test_vec_from_vecdeque() {
    use crate::vec::Vec;

    fn create_vec_and_test_convert(capacity: usize, offset: usize, len: usize) {
        let mut vd = VecDeque::with_capacity(capacity);
        for _ in 0..offset {
            vd.push_back(0);
            vd.pop_front();
        }
        vd.extend(0..len);

        let vec: Vec<_> = Vec::from(vd.clone());
        assert_eq!(vec.len(), vd.len());
        assert!(vec.into_iter().eq(vd));
    }

    #[cfg(not(miri))] // Miri is too slow
    let max_pwr = 7;
    #[cfg(miri)]
    let max_pwr = 5;

    for cap_pwr in 0..max_pwr {
        // Make capacity as a (2^x)-1, so that the ring size is 2^x
        let cap = (2i32.pow(cap_pwr) - 1) as usize;

        // In these cases there is enough free space to solve it with copies
        for len in 0..((cap + 1) / 2) {
            // Test contiguous cases
            for offset in 0..(cap - len) {
                create_vec_and_test_convert(cap, offset, len)
            }

            // Test cases where block at end of buffer is bigger than block at start
            for offset in (cap - len)..(cap - (len / 2)) {
                create_vec_and_test_convert(cap, offset, len)
            }

            // Test cases where block at start of buffer is bigger than block at end
            for offset in (cap - (len / 2))..cap {
                create_vec_and_test_convert(cap, offset, len)
            }
        }

        // Now there's not (necessarily) space to straighten the ring with simple copies,
        // the ring will use swapping when:
        // (cap + 1 - offset) > (cap + 1 - len) && (len - (cap + 1 - offset)) > (cap + 1 - len))
        //  right block size  >   free space    &&      left block size       >    free space
        for len in ((cap + 1) / 2)..cap {
            // Test contiguous cases
            for offset in 0..(cap - len) {
                create_vec_and_test_convert(cap, offset, len)
            }

            // Test cases where block at end of buffer is bigger than block at start
            for offset in (cap - len)..(cap - (len / 2)) {
                create_vec_and_test_convert(cap, offset, len)
            }

            // Test cases where block at start of buffer is bigger than block at end
            for offset in (cap - (len / 2))..cap {
                create_vec_and_test_convert(cap, offset, len)
            }
        }
    }
}

#[test]
fn issue_53529() {
    use crate::boxed::Box;

    let mut dst = VecDeque::new();
    dst.push_front(Box::new(1));
    dst.push_front(Box::new(2));
    assert_eq!(*dst.pop_back().unwrap(), 1);

    let mut src = VecDeque::new();
    src.push_front(Box::new(2));
    dst.append(&mut src);
    for a in dst {
        assert_eq!(*a, 2);
    }
}
