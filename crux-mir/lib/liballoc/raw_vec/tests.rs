use super::*;

#[test]
fn allocator_param() {
    use crate::alloc::AllocErr;

    // Writing a test of integration between third-party
    // allocators and `RawVec` is a little tricky because the `RawVec`
    // API does not expose fallible allocation methods, so we
    // cannot check what happens when allocator is exhausted
    // (beyond detecting a panic).
    //
    // Instead, this just checks that the `RawVec` methods do at
    // least go through the Allocator API when it reserves
    // storage.

    // A dumb allocator that consumes a fixed amount of fuel
    // before allocation attempts start failing.
    struct BoundedAlloc {
        fuel: usize,
    }
    unsafe impl AllocRef for BoundedAlloc {
        fn alloc(&mut self, layout: Layout) -> Result<(NonNull<u8>, usize), AllocErr> {
            let size = layout.size();
            if size > self.fuel {
                return Err(AllocErr);
            }
            match Global.alloc(layout) {
                ok @ Ok(_) => {
                    self.fuel -= size;
                    ok
                }
                err @ Err(_) => err,
            }
        }
        unsafe fn dealloc(&mut self, ptr: NonNull<u8>, layout: Layout) {
            Global.dealloc(ptr, layout)
        }
    }

    let a = BoundedAlloc { fuel: 500 };
    let mut v: RawVec<u8, _> = RawVec::with_capacity_in(50, a);
    assert_eq!(v.a.fuel, 450);
    v.reserve(50, 150); // (causes a realloc, thus using 50 + 150 = 200 units of fuel)
    assert_eq!(v.a.fuel, 250);
}

#[test]
fn reserve_does_not_overallocate() {
    {
        let mut v: RawVec<u32> = RawVec::new();
        // First, `reserve` allocates like `reserve_exact`.
        v.reserve(0, 9);
        assert_eq!(9, v.capacity());
    }

    {
        let mut v: RawVec<u32> = RawVec::new();
        v.reserve(0, 7);
        assert_eq!(7, v.capacity());
        // 97 if more than double of 7, so `reserve` should work
        // like `reserve_exact`.
        v.reserve(7, 90);
        assert_eq!(97, v.capacity());
    }

    {
        let mut v: RawVec<u32> = RawVec::new();
        v.reserve(0, 12);
        assert_eq!(12, v.capacity());
        v.reserve(12, 3);
        // 3 is less than half of 12, so `reserve` must grow
        // exponentially. At the time of writing this test grow
        // factor is 2, so new capacity is 24, however, grow factor
        // of 1.5 is OK too. Hence `>= 18` in assert.
        assert!(v.capacity() >= 12 + 12 / 2);
    }
}
