use super::*;

use std::boxed::Box;
use std::clone::Clone;
use std::convert::{From, TryInto};
use std::mem::drop;
use std::ops::Drop;
use std::option::Option::{self, None, Some};
use std::sync::atomic::{
    self,
    Ordering::{Acquire, SeqCst},
};
use std::sync::mpsc::channel;
use std::sync::Mutex;
use std::thread;

use crate::vec::Vec;

struct Canary(*mut atomic::AtomicUsize);

impl Drop for Canary {
    fn drop(&mut self) {
        unsafe {
            match *self {
                Canary(c) => {
                    (*c).fetch_add(1, SeqCst);
                }
            }
        }
    }
}

#[test]
#[cfg_attr(target_os = "emscripten", ignore)]
#[cfg_attr(miri, ignore)] // Miri does not support threads
fn manually_share_arc() {
    let v = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    let arc_v = Arc::new(v);

    let (tx, rx) = channel();

    let _t = thread::spawn(move || {
        let arc_v: Arc<Vec<i32>> = rx.recv().unwrap();
        assert_eq!((*arc_v)[3], 4);
    });

    tx.send(arc_v.clone()).unwrap();

    assert_eq!((*arc_v)[2], 3);
    assert_eq!((*arc_v)[4], 5);
}

#[test]
fn test_arc_get_mut() {
    let mut x = Arc::new(3);
    *Arc::get_mut(&mut x).unwrap() = 4;
    assert_eq!(*x, 4);
    let y = x.clone();
    assert!(Arc::get_mut(&mut x).is_none());
    drop(y);
    assert!(Arc::get_mut(&mut x).is_some());
    let _w = Arc::downgrade(&x);
    assert!(Arc::get_mut(&mut x).is_none());
}

#[test]
fn weak_counts() {
    assert_eq!(Weak::weak_count(&Weak::<u64>::new()), 0);
    assert_eq!(Weak::strong_count(&Weak::<u64>::new()), 0);

    let a = Arc::new(0);
    let w = Arc::downgrade(&a);
    assert_eq!(Weak::strong_count(&w), 1);
    assert_eq!(Weak::weak_count(&w), 1);
    let w2 = w.clone();
    assert_eq!(Weak::strong_count(&w), 1);
    assert_eq!(Weak::weak_count(&w), 2);
    assert_eq!(Weak::strong_count(&w2), 1);
    assert_eq!(Weak::weak_count(&w2), 2);
    drop(w);
    assert_eq!(Weak::strong_count(&w2), 1);
    assert_eq!(Weak::weak_count(&w2), 1);
    let a2 = a.clone();
    assert_eq!(Weak::strong_count(&w2), 2);
    assert_eq!(Weak::weak_count(&w2), 1);
    drop(a2);
    drop(a);
    assert_eq!(Weak::strong_count(&w2), 0);
    assert_eq!(Weak::weak_count(&w2), 0);
    drop(w2);
}

#[test]
fn try_unwrap() {
    let x = Arc::new(3);
    assert_eq!(Arc::try_unwrap(x), Ok(3));
    let x = Arc::new(4);
    let _y = x.clone();
    assert_eq!(Arc::try_unwrap(x), Err(Arc::new(4)));
    let x = Arc::new(5);
    let _w = Arc::downgrade(&x);
    assert_eq!(Arc::try_unwrap(x), Ok(5));
}

#[test]
fn into_from_raw() {
    let x = Arc::new(box "hello");
    let y = x.clone();

    let x_ptr = Arc::into_raw(x);
    drop(y);
    unsafe {
        assert_eq!(**x_ptr, "hello");

        let x = Arc::from_raw(x_ptr);
        assert_eq!(**x, "hello");

        assert_eq!(Arc::try_unwrap(x).map(|x| *x), Ok("hello"));
    }
}

#[test]
fn test_into_from_raw_unsized() {
    use std::fmt::Display;
    use std::string::ToString;

    let arc: Arc<str> = Arc::from("foo");

    let ptr = Arc::into_raw(arc.clone());
    let arc2 = unsafe { Arc::from_raw(ptr) };

    assert_eq!(unsafe { &*ptr }, "foo");
    assert_eq!(arc, arc2);

    let arc: Arc<dyn Display> = Arc::new(123);

    let ptr = Arc::into_raw(arc.clone());
    let arc2 = unsafe { Arc::from_raw(ptr) };

    assert_eq!(unsafe { &*ptr }.to_string(), "123");
    assert_eq!(arc2.to_string(), "123");
}

#[test]
fn test_cowarc_clone_make_mut() {
    let mut cow0 = Arc::new(75);
    let mut cow1 = cow0.clone();
    let mut cow2 = cow1.clone();

    assert!(75 == *Arc::make_mut(&mut cow0));
    assert!(75 == *Arc::make_mut(&mut cow1));
    assert!(75 == *Arc::make_mut(&mut cow2));

    *Arc::make_mut(&mut cow0) += 1;
    *Arc::make_mut(&mut cow1) += 2;
    *Arc::make_mut(&mut cow2) += 3;

    assert!(76 == *cow0);
    assert!(77 == *cow1);
    assert!(78 == *cow2);

    // none should point to the same backing memory
    assert!(*cow0 != *cow1);
    assert!(*cow0 != *cow2);
    assert!(*cow1 != *cow2);
}

#[test]
fn test_cowarc_clone_unique2() {
    let mut cow0 = Arc::new(75);
    let cow1 = cow0.clone();
    let cow2 = cow1.clone();

    assert!(75 == *cow0);
    assert!(75 == *cow1);
    assert!(75 == *cow2);

    *Arc::make_mut(&mut cow0) += 1;
    assert!(76 == *cow0);
    assert!(75 == *cow1);
    assert!(75 == *cow2);

    // cow1 and cow2 should share the same contents
    // cow0 should have a unique reference
    assert!(*cow0 != *cow1);
    assert!(*cow0 != *cow2);
    assert!(*cow1 == *cow2);
}

#[test]
fn test_cowarc_clone_weak() {
    let mut cow0 = Arc::new(75);
    let cow1_weak = Arc::downgrade(&cow0);

    assert!(75 == *cow0);
    assert!(75 == *cow1_weak.upgrade().unwrap());

    *Arc::make_mut(&mut cow0) += 1;

    assert!(76 == *cow0);
    assert!(cow1_weak.upgrade().is_none());
}

#[test]
fn test_live() {
    let x = Arc::new(5);
    let y = Arc::downgrade(&x);
    assert!(y.upgrade().is_some());
}

#[test]
fn test_dead() {
    let x = Arc::new(5);
    let y = Arc::downgrade(&x);
    drop(x);
    assert!(y.upgrade().is_none());
}

#[test]
fn weak_self_cyclic() {
    struct Cycle {
        x: Mutex<Option<Weak<Cycle>>>,
    }

    let a = Arc::new(Cycle { x: Mutex::new(None) });
    let b = Arc::downgrade(&a.clone());
    *a.x.lock().unwrap() = Some(b);

    // hopefully we don't double-free (or leak)...
}

#[test]
fn drop_arc() {
    let mut canary = atomic::AtomicUsize::new(0);
    let x = Arc::new(Canary(&mut canary as *mut atomic::AtomicUsize));
    drop(x);
    assert!(canary.load(Acquire) == 1);
}

#[test]
fn drop_arc_weak() {
    let mut canary = atomic::AtomicUsize::new(0);
    let arc = Arc::new(Canary(&mut canary as *mut atomic::AtomicUsize));
    let arc_weak = Arc::downgrade(&arc);
    assert!(canary.load(Acquire) == 0);
    drop(arc);
    assert!(canary.load(Acquire) == 1);
    drop(arc_weak);
}

#[test]
fn test_strong_count() {
    let a = Arc::new(0);
    assert!(Arc::strong_count(&a) == 1);
    let w = Arc::downgrade(&a);
    assert!(Arc::strong_count(&a) == 1);
    let b = w.upgrade().expect("");
    assert!(Arc::strong_count(&b) == 2);
    assert!(Arc::strong_count(&a) == 2);
    drop(w);
    drop(a);
    assert!(Arc::strong_count(&b) == 1);
    let c = b.clone();
    assert!(Arc::strong_count(&b) == 2);
    assert!(Arc::strong_count(&c) == 2);
}

#[test]
fn test_weak_count() {
    let a = Arc::new(0);
    assert!(Arc::strong_count(&a) == 1);
    assert!(Arc::weak_count(&a) == 0);
    let w = Arc::downgrade(&a);
    assert!(Arc::strong_count(&a) == 1);
    assert!(Arc::weak_count(&a) == 1);
    let x = w.clone();
    assert!(Arc::weak_count(&a) == 2);
    drop(w);
    drop(x);
    assert!(Arc::strong_count(&a) == 1);
    assert!(Arc::weak_count(&a) == 0);
    let c = a.clone();
    assert!(Arc::strong_count(&a) == 2);
    assert!(Arc::weak_count(&a) == 0);
    let d = Arc::downgrade(&c);
    assert!(Arc::weak_count(&c) == 1);
    assert!(Arc::strong_count(&c) == 2);

    drop(a);
    drop(c);
    drop(d);
}

#[test]
fn show_arc() {
    let a = Arc::new(5);
    assert_eq!(format!("{:?}", a), "5");
}

// Make sure deriving works with Arc<T>
#[derive(Eq, Ord, PartialEq, PartialOrd, Clone, Debug, Default)]
struct Foo {
    inner: Arc<i32>,
}

#[test]
fn test_unsized() {
    let x: Arc<[i32]> = Arc::new([1, 2, 3]);
    assert_eq!(format!("{:?}", x), "[1, 2, 3]");
    let y = Arc::downgrade(&x.clone());
    drop(x);
    assert!(y.upgrade().is_none());
}

#[test]
fn test_from_owned() {
    let foo = 123;
    let foo_arc = Arc::from(foo);
    assert!(123 == *foo_arc);
}

#[test]
fn test_new_weak() {
    let foo: Weak<usize> = Weak::new();
    assert!(foo.upgrade().is_none());
}

#[test]
fn test_ptr_eq() {
    let five = Arc::new(5);
    let same_five = five.clone();
    let other_five = Arc::new(5);

    assert!(Arc::ptr_eq(&five, &same_five));
    assert!(!Arc::ptr_eq(&five, &other_five));
}

#[test]
#[cfg_attr(target_os = "emscripten", ignore)]
#[cfg_attr(miri, ignore)] // Miri does not support threads
fn test_weak_count_locked() {
    let mut a = Arc::new(atomic::AtomicBool::new(false));
    let a2 = a.clone();
    let t = thread::spawn(move || {
        for _i in 0..1000000 {
            Arc::get_mut(&mut a);
        }
        a.store(true, SeqCst);
    });

    while !a2.load(SeqCst) {
        let n = Arc::weak_count(&a2);
        assert!(n < 2, "bad weak count: {}", n);
    }
    t.join().unwrap();
}

#[test]
fn test_from_str() {
    let r: Arc<str> = Arc::from("foo");

    assert_eq!(&r[..], "foo");
}

#[test]
fn test_copy_from_slice() {
    let s: &[u32] = &[1, 2, 3];
    let r: Arc<[u32]> = Arc::from(s);

    assert_eq!(&r[..], [1, 2, 3]);
}

#[test]
fn test_clone_from_slice() {
    #[derive(Clone, Debug, Eq, PartialEq)]
    struct X(u32);

    let s: &[X] = &[X(1), X(2), X(3)];
    let r: Arc<[X]> = Arc::from(s);

    assert_eq!(&r[..], s);
}

#[test]
#[should_panic]
fn test_clone_from_slice_panic() {
    use std::string::{String, ToString};

    struct Fail(u32, String);

    impl Clone for Fail {
        fn clone(&self) -> Fail {
            if self.0 == 2 {
                panic!();
            }
            Fail(self.0, self.1.clone())
        }
    }

    let s: &[Fail] =
        &[Fail(0, "foo".to_string()), Fail(1, "bar".to_string()), Fail(2, "baz".to_string())];

    // Should panic, but not cause memory corruption
    let _r: Arc<[Fail]> = Arc::from(s);
}

#[test]
fn test_from_box() {
    let b: Box<u32> = box 123;
    let r: Arc<u32> = Arc::from(b);

    assert_eq!(*r, 123);
}

#[test]
fn test_from_box_str() {
    use std::string::String;

    let s = String::from("foo").into_boxed_str();
    let r: Arc<str> = Arc::from(s);

    assert_eq!(&r[..], "foo");
}

#[test]
fn test_from_box_slice() {
    let s = vec![1, 2, 3].into_boxed_slice();
    let r: Arc<[u32]> = Arc::from(s);

    assert_eq!(&r[..], [1, 2, 3]);
}

#[test]
fn test_from_box_trait() {
    use std::fmt::Display;
    use std::string::ToString;

    let b: Box<dyn Display> = box 123;
    let r: Arc<dyn Display> = Arc::from(b);

    assert_eq!(r.to_string(), "123");
}

#[test]
fn test_from_box_trait_zero_sized() {
    use std::fmt::Debug;

    let b: Box<dyn Debug> = box ();
    let r: Arc<dyn Debug> = Arc::from(b);

    assert_eq!(format!("{:?}", r), "()");
}

#[test]
fn test_from_vec() {
    let v = vec![1, 2, 3];
    let r: Arc<[u32]> = Arc::from(v);

    assert_eq!(&r[..], [1, 2, 3]);
}

#[test]
fn test_downcast() {
    use std::any::Any;

    let r1: Arc<dyn Any + Send + Sync> = Arc::new(i32::max_value());
    let r2: Arc<dyn Any + Send + Sync> = Arc::new("abc");

    assert!(r1.clone().downcast::<u32>().is_err());

    let r1i32 = r1.downcast::<i32>();
    assert!(r1i32.is_ok());
    assert_eq!(r1i32.unwrap(), Arc::new(i32::max_value()));

    assert!(r2.clone().downcast::<i32>().is_err());

    let r2str = r2.downcast::<&'static str>();
    assert!(r2str.is_ok());
    assert_eq!(r2str.unwrap(), Arc::new("abc"));
}

#[test]
fn test_array_from_slice() {
    let v = vec![1, 2, 3];
    let r: Arc<[u32]> = Arc::from(v);

    let a: Result<Arc<[u32; 3]>, _> = r.clone().try_into();
    assert!(a.is_ok());

    let a: Result<Arc<[u32; 2]>, _> = r.clone().try_into();
    assert!(a.is_err());
}
