#[cfg(target_arch = "wasm32")]
use core::arch::wasm32 as wasm;
#[cfg(target_arch = "wasm64")]
use core::arch::wasm64 as wasm;
use core::ptr;
use Allocator;

/// System setting for Wasm
pub struct System {
    _priv: (),
}

impl System {
    pub const fn new() -> System {
        System { _priv: () }
    }
}

unsafe impl Allocator for System {
    fn alloc(&self, size: usize) -> (*mut u8, usize, u32) {
        let pages = size / self.page_size();
        let prev = wasm::memory_grow(0, pages);
        if prev == usize::max_value() {
            return (ptr::null_mut(), 0, 0);
        }
        (
            (prev * self.page_size()) as *mut u8,
            pages * self.page_size(),
            0,
        )
    }

    fn remap(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize, _can_move: bool) -> *mut u8 {
        // TODO: I think this can be implemented near the end?
        ptr::null_mut()
    }

    fn free_part(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize) -> bool {
        false
    }

    fn free(&self, _ptr: *mut u8, _size: usize) -> bool {
        false
    }

    fn can_release_part(&self, _flags: u32) -> bool {
        false
    }

    fn allocates_zeros(&self) -> bool {
        true
    }

    fn page_size(&self) -> usize {
        64 * 1024
    }
}

#[cfg(feature = "global")]
pub fn acquire_global_lock() {
    // single threaded, no need!
}

#[cfg(feature = "global")]
pub fn release_global_lock() {
    // single threaded, no need!
}

#[cfg(feature = "global")]
pub unsafe fn enable_alloc_after_fork() {
    // single threaded, no need!
}
