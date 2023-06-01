use crate::cell::Cell;

pub struct RWLock {
    num_readers: Cell<usize>,
    write_locked: Cell<bool>,
}

unsafe impl Send for RWLock {}
unsafe impl Sync for RWLock {}

impl RWLock {
    pub const fn new() -> RWLock {
        RWLock {
            num_readers: Cell::new(0),
            write_locked: Cell::new(false),
        }
    }
    #[inline]
    pub unsafe fn read(&self) {
        // TODO: Currently, we never run `drop` code, so locks are never released.  Once we support
        // drops, we can enable this assertion to check for invalid usage.
        //assert!(!self.write_locked.get());
        self.num_readers.set(self.num_readers.get() + 1);
    }

    #[inline]
    pub unsafe fn try_read(&self) -> bool {
        if self.write_locked.get() {
            false
        } else {
            self.read();
            true
        }
    }

    #[inline]
    pub unsafe fn write(&self) {
        // TODO: Currently, we never run `drop` code, so locks are never released.  Once we support
        // drops, we can enable this assertion to check for invalid usage.
        //assert!(!self.write_locked.get());
        //assert!(self.num_readers.get() == 0);
        self.write_locked.set(true);
    }

    #[inline]
    pub unsafe fn try_write(&self) -> bool {
        if self.write_locked.get() || self.num_readers.get() > 0 {
            false
        } else {
            self.write();
            true
        }
    }

    #[inline]
    pub unsafe fn read_unlock(&self) {
        self.num_readers.set(self.num_readers.get() - 1);
    }

    #[inline]
    pub unsafe fn write_unlock(&self) {
        assert!(self.write_locked.get());
        self.write_locked.set(false);
    }

    #[inline]
    pub unsafe fn destroy(&self) {
        // No-op
    }
}
