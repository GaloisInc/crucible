use std::collections::binary_heap::{Drain, PeekMut};
use std::collections::BinaryHeap;
use std::iter::TrustedLen;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::sync::atomic::{AtomicU32, Ordering};

#[test]
fn test_iterator() {
    let data = vec![5, 9, 3];
    let iterout = [9, 5, 3];
    let heap = BinaryHeap::from(data);
    let mut i = 0;
    for el in &heap {
        assert_eq!(*el, iterout[i]);
        i += 1;
    }
}

#[test]
fn test_iter_rev_cloned_collect() {
    let data = vec![5, 9, 3];
    let iterout = vec![3, 5, 9];
    let pq = BinaryHeap::from(data);

    let v: Vec<_> = pq.iter().rev().cloned().collect();
    assert_eq!(v, iterout);
}

#[test]
fn test_into_iter_collect() {
    let data = vec![5, 9, 3];
    let iterout = vec![9, 5, 3];
    let pq = BinaryHeap::from(data);

    let v: Vec<_> = pq.into_iter().collect();
    assert_eq!(v, iterout);
}

#[test]
fn test_into_iter_size_hint() {
    let data = vec![5, 9];
    let pq = BinaryHeap::from(data);

    let mut it = pq.into_iter();

    assert_eq!(it.size_hint(), (2, Some(2)));
    assert_eq!(it.next(), Some(9));

    assert_eq!(it.size_hint(), (1, Some(1)));
    assert_eq!(it.next(), Some(5));

    assert_eq!(it.size_hint(), (0, Some(0)));
    assert_eq!(it.next(), None);
}

#[test]
fn test_into_iter_rev_collect() {
    let data = vec![5, 9, 3];
    let iterout = vec![3, 5, 9];
    let pq = BinaryHeap::from(data);

    let v: Vec<_> = pq.into_iter().rev().collect();
    assert_eq!(v, iterout);
}

#[test]
fn test_into_iter_sorted_collect() {
    let heap = BinaryHeap::from(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
    let it = heap.into_iter_sorted();
    let sorted = it.collect::<Vec<_>>();
    assert_eq!(sorted, vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 2, 1, 1, 0]);
}

#[test]
fn test_drain_sorted_collect() {
    let mut heap = BinaryHeap::from(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
    let it = heap.drain_sorted();
    let sorted = it.collect::<Vec<_>>();
    assert_eq!(sorted, vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 2, 1, 1, 0]);
}

fn check_exact_size_iterator<I: ExactSizeIterator>(len: usize, it: I) {
    let mut it = it;

    for i in 0..it.len() {
        let (lower, upper) = it.size_hint();
        assert_eq!(Some(lower), upper);
        assert_eq!(lower, len - i);
        assert_eq!(it.len(), len - i);
        it.next();
    }
    assert_eq!(it.len(), 0);
    assert!(it.is_empty());
}

#[test]
fn test_exact_size_iterator() {
    let heap = BinaryHeap::from(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
    check_exact_size_iterator(heap.len(), heap.iter());
    check_exact_size_iterator(heap.len(), heap.clone().into_iter());
    check_exact_size_iterator(heap.len(), heap.clone().into_iter_sorted());
    check_exact_size_iterator(heap.len(), heap.clone().drain());
    check_exact_size_iterator(heap.len(), heap.clone().drain_sorted());
}

fn check_trusted_len<I: TrustedLen>(len: usize, it: I) {
    let mut it = it;
    for i in 0..len {
        let (lower, upper) = it.size_hint();
        if upper.is_some() {
            assert_eq!(Some(lower), upper);
            assert_eq!(lower, len - i);
        }
        it.next();
    }
}

#[test]
fn test_trusted_len() {
    let heap = BinaryHeap::from(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
    check_trusted_len(heap.len(), heap.clone().into_iter_sorted());
    check_trusted_len(heap.len(), heap.clone().drain_sorted());
}

#[test]
fn test_peek_and_pop() {
    let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
    let mut sorted = data.clone();
    sorted.sort();
    let mut heap = BinaryHeap::from(data);
    while !heap.is_empty() {
        assert_eq!(heap.peek().unwrap(), sorted.last().unwrap());
        assert_eq!(heap.pop().unwrap(), sorted.pop().unwrap());
    }
}

#[test]
fn test_peek_mut() {
    let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
    let mut heap = BinaryHeap::from(data);
    assert_eq!(heap.peek(), Some(&10));
    {
        let mut top = heap.peek_mut().unwrap();
        *top -= 2;
    }
    assert_eq!(heap.peek(), Some(&9));
}

#[test]
fn test_peek_mut_pop() {
    let data = vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1];
    let mut heap = BinaryHeap::from(data);
    assert_eq!(heap.peek(), Some(&10));
    {
        let mut top = heap.peek_mut().unwrap();
        *top -= 2;
        assert_eq!(PeekMut::pop(top), 8);
    }
    assert_eq!(heap.peek(), Some(&9));
}

#[test]
fn test_push() {
    let mut heap = BinaryHeap::from(vec![2, 4, 9]);
    assert_eq!(heap.len(), 3);
    assert!(*heap.peek().unwrap() == 9);
    heap.push(11);
    assert_eq!(heap.len(), 4);
    assert!(*heap.peek().unwrap() == 11);
    heap.push(5);
    assert_eq!(heap.len(), 5);
    assert!(*heap.peek().unwrap() == 11);
    heap.push(27);
    assert_eq!(heap.len(), 6);
    assert!(*heap.peek().unwrap() == 27);
    heap.push(3);
    assert_eq!(heap.len(), 7);
    assert!(*heap.peek().unwrap() == 27);
    heap.push(103);
    assert_eq!(heap.len(), 8);
    assert!(*heap.peek().unwrap() == 103);
}

#[test]
fn test_push_unique() {
    let mut heap = BinaryHeap::<Box<_>>::from(vec![box 2, box 4, box 9]);
    assert_eq!(heap.len(), 3);
    assert!(**heap.peek().unwrap() == 9);
    heap.push(box 11);
    assert_eq!(heap.len(), 4);
    assert!(**heap.peek().unwrap() == 11);
    heap.push(box 5);
    assert_eq!(heap.len(), 5);
    assert!(**heap.peek().unwrap() == 11);
    heap.push(box 27);
    assert_eq!(heap.len(), 6);
    assert!(**heap.peek().unwrap() == 27);
    heap.push(box 3);
    assert_eq!(heap.len(), 7);
    assert!(**heap.peek().unwrap() == 27);
    heap.push(box 103);
    assert_eq!(heap.len(), 8);
    assert!(**heap.peek().unwrap() == 103);
}

fn check_to_vec(mut data: Vec<i32>) {
    let heap = BinaryHeap::from(data.clone());
    let mut v = heap.clone().into_vec();
    v.sort();
    data.sort();

    assert_eq!(v, data);
    assert_eq!(heap.into_sorted_vec(), data);
}

#[test]
fn test_to_vec() {
    check_to_vec(vec![]);
    check_to_vec(vec![5]);
    check_to_vec(vec![3, 2]);
    check_to_vec(vec![2, 3]);
    check_to_vec(vec![5, 1, 2]);
    check_to_vec(vec![1, 100, 2, 3]);
    check_to_vec(vec![1, 3, 5, 7, 9, 2, 4, 6, 8, 0]);
    check_to_vec(vec![2, 4, 6, 2, 1, 8, 10, 3, 5, 7, 0, 9, 1]);
    check_to_vec(vec![9, 11, 9, 9, 9, 9, 11, 2, 3, 4, 11, 9, 0, 0, 0, 0]);
    check_to_vec(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    check_to_vec(vec![10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]);
    check_to_vec(vec![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 0, 0, 0, 1, 2]);
    check_to_vec(vec![5, 4, 3, 2, 1, 5, 4, 3, 2, 1, 5, 4, 3, 2, 1]);
}

#[test]
fn test_empty_pop() {
    let mut heap = BinaryHeap::<i32>::new();
    assert!(heap.pop().is_none());
}

#[test]
fn test_empty_peek() {
    let empty = BinaryHeap::<i32>::new();
    assert!(empty.peek().is_none());
}

#[test]
fn test_empty_peek_mut() {
    let mut empty = BinaryHeap::<i32>::new();
    assert!(empty.peek_mut().is_none());
}

#[test]
fn test_from_iter() {
    let xs = vec![9, 8, 7, 6, 5, 4, 3, 2, 1];

    let mut q: BinaryHeap<_> = xs.iter().rev().cloned().collect();

    for &x in &xs {
        assert_eq!(q.pop().unwrap(), x);
    }
}

#[test]
fn test_drain() {
    let mut q: BinaryHeap<_> = [9, 8, 7, 6, 5, 4, 3, 2, 1].iter().cloned().collect();

    assert_eq!(q.drain().take(5).count(), 5);

    assert!(q.is_empty());
}

#[test]
fn test_drain_sorted() {
    let mut q: BinaryHeap<_> = [9, 8, 7, 6, 5, 4, 3, 2, 1].iter().cloned().collect();

    assert_eq!(q.drain_sorted().take(5).collect::<Vec<_>>(), vec![9, 8, 7, 6, 5]);

    assert!(q.is_empty());
}

#[test]
fn test_drain_sorted_leak() {
    static DROPS: AtomicU32 = AtomicU32::new(0);

    #[derive(Clone, PartialEq, Eq, PartialOrd, Ord)]
    struct D(u32, bool);

    impl Drop for D {
        fn drop(&mut self) {
            DROPS.fetch_add(1, Ordering::SeqCst);

            if self.1 {
                panic!("panic in `drop`");
            }
        }
    }

    let mut q = BinaryHeap::from(vec![
        D(0, false),
        D(1, false),
        D(2, false),
        D(3, true),
        D(4, false),
        D(5, false),
    ]);

    catch_unwind(AssertUnwindSafe(|| drop(q.drain_sorted()))).ok();

    assert_eq!(DROPS.load(Ordering::SeqCst), 6);
}

#[test]
fn test_extend_ref() {
    let mut a = BinaryHeap::new();
    a.push(1);
    a.push(2);

    a.extend(&[3, 4, 5]);

    assert_eq!(a.len(), 5);
    assert_eq!(a.into_sorted_vec(), [1, 2, 3, 4, 5]);

    let mut a = BinaryHeap::new();
    a.push(1);
    a.push(2);
    let mut b = BinaryHeap::new();
    b.push(3);
    b.push(4);
    b.push(5);

    a.extend(&b);

    assert_eq!(a.len(), 5);
    assert_eq!(a.into_sorted_vec(), [1, 2, 3, 4, 5]);
}

#[test]
fn test_append() {
    let mut a = BinaryHeap::from(vec![-10, 1, 2, 3, 3]);
    let mut b = BinaryHeap::from(vec![-20, 5, 43]);

    a.append(&mut b);

    assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
    assert!(b.is_empty());
}

#[test]
fn test_append_to_empty() {
    let mut a = BinaryHeap::new();
    let mut b = BinaryHeap::from(vec![-20, 5, 43]);

    a.append(&mut b);

    assert_eq!(a.into_sorted_vec(), [-20, 5, 43]);
    assert!(b.is_empty());
}

#[test]
fn test_extend_specialization() {
    let mut a = BinaryHeap::from(vec![-10, 1, 2, 3, 3]);
    let b = BinaryHeap::from(vec![-20, 5, 43]);

    a.extend(b);

    assert_eq!(a.into_sorted_vec(), [-20, -10, 1, 2, 3, 3, 5, 43]);
}

#[allow(dead_code)]
fn assert_covariance() {
    fn drain<'new>(d: Drain<'static, &'static str>) -> Drain<'new, &'new str> {
        d
    }
}

// old binaryheap failed this test
//
// Integrity means that all elements are present after a comparison panics,
// even if the order may not be correct.
//
// Destructors must be called exactly once per element.
// FIXME: re-enable emscripten once it can unwind again
#[test]
#[cfg(not(target_os = "emscripten"))]
fn panic_safe() {
    use rand::{seq::SliceRandom, thread_rng};
    use std::cmp;
    use std::panic::{self, AssertUnwindSafe};
    use std::sync::atomic::{AtomicUsize, Ordering};

    static DROP_COUNTER: AtomicUsize = AtomicUsize::new(0);

    #[derive(Eq, PartialEq, Ord, Clone, Debug)]
    struct PanicOrd<T>(T, bool);

    impl<T> Drop for PanicOrd<T> {
        fn drop(&mut self) {
            // update global drop count
            DROP_COUNTER.fetch_add(1, Ordering::SeqCst);
        }
    }

    impl<T: PartialOrd> PartialOrd for PanicOrd<T> {
        fn partial_cmp(&self, other: &Self) -> Option<cmp::Ordering> {
            if self.1 || other.1 {
                panic!("Panicking comparison");
            }
            self.0.partial_cmp(&other.0)
        }
    }
    let mut rng = thread_rng();
    const DATASZ: usize = 32;
    #[cfg(not(miri))] // Miri is too slow
    const NTEST: usize = 10;
    #[cfg(miri)]
    const NTEST: usize = 1;

    // don't use 0 in the data -- we want to catch the zeroed-out case.
    let data = (1..=DATASZ).collect::<Vec<_>>();

    // since it's a fuzzy test, run several tries.
    for _ in 0..NTEST {
        for i in 1..=DATASZ {
            DROP_COUNTER.store(0, Ordering::SeqCst);

            let mut panic_ords: Vec<_> =
                data.iter().filter(|&&x| x != i).map(|&x| PanicOrd(x, false)).collect();
            let panic_item = PanicOrd(i, true);

            // heapify the sane items
            panic_ords.shuffle(&mut rng);
            let mut heap = BinaryHeap::from(panic_ords);
            let inner_data;

            {
                // push the panicking item to the heap and catch the panic
                let thread_result = {
                    let mut heap_ref = AssertUnwindSafe(&mut heap);
                    panic::catch_unwind(move || {
                        heap_ref.push(panic_item);
                    })
                };
                assert!(thread_result.is_err());

                // Assert no elements were dropped
                let drops = DROP_COUNTER.load(Ordering::SeqCst);
                assert!(drops == 0, "Must not drop items. drops={}", drops);
                inner_data = heap.clone().into_vec();
                drop(heap);
            }
            let drops = DROP_COUNTER.load(Ordering::SeqCst);
            assert_eq!(drops, DATASZ);

            let mut data_sorted = inner_data.into_iter().map(|p| p.0).collect::<Vec<_>>();
            data_sorted.sort();
            assert_eq!(data_sorted, data);
        }
    }
}
