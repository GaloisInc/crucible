#![allow(dead_code)]
use crate::cell::Cell;
use crate::mem;
use core::crucible::concurrency;

pub struct Mutex {
    locked: Cell<bool>,
}

unsafe impl Send for Mutex {}
unsafe impl Sync for Mutex {}

impl Mutex {
    pub const fn new() -> Mutex {
        Mutex {
            locked: Cell::new(false),
        }
    }
    #[inline]
    pub unsafe fn init(&mut self) {
        // No-op
    }
    #[inline]
    pub unsafe fn lock(&self) {
        // TODO: Currently, we never run `drop` code, so locks are never released.  Once we support
        // drops, we can enable this assertion to check for (invalid) reentrant locking.
        // assert!(!self.locked.get());
        concurrency::mutex_lock(self);
        self.locked.set(true); //TODO: Why does this yield an empty mux tree in crux?
    }
    #[inline]
    pub unsafe fn unlock(&self) {
        // TODO: Currently, we never run `drop` code, so locks are never released.  Once we support
        // drops, we can enable this assertion to check for invalid usage.
        concurrency::mutex_unlock(self);
        // assert!(self.locked.get());
        self.locked.set(false);
    }
    #[inline]
    pub unsafe fn try_lock(&self) -> bool {
        if self.locked.get() {
            false
        } else {
            self.locked.set(true);
            true
        }
    }
    #[inline]
    pub unsafe fn destroy(&self) {
        // No-op
    }
}

pub struct ReentrantMutex {
    lock_count: Cell<usize>,
}

unsafe impl Send for ReentrantMutex {}
unsafe impl Sync for ReentrantMutex {}

impl ReentrantMutex {
    pub const unsafe fn uninitialized() -> ReentrantMutex {
        ReentrantMutex {
            lock_count: Cell::new(0),
        }
    }

    #[inline]
    pub unsafe fn init(&self) {
        // No-op
    }

    #[inline]
    pub unsafe fn lock(&self) {
        self.lock_count.set(self.lock_count.get() + 1);
    }

    #[inline]
    pub unsafe fn try_lock(&self) -> bool {
        // There is only one thread, so locking cannot fail.
        self.lock();
        true
    }

    #[inline]
    pub unsafe fn unlock(&self) {
        self.lock_count.set(self.lock_count.get() - 1);
    }

    #[inline]
    pub unsafe fn destroy(&self) {
        // No-op
    }
}
