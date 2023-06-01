use crate::sys::crux::mutex::Mutex;
use crate::time::Duration;

pub struct Condvar {
}

unsafe impl Send for Condvar {}
unsafe impl Sync for Condvar {}

impl Condvar {
    pub const fn new() -> Condvar {
        Condvar {}
    }

    pub fn init(&mut self) {
        // No-op
    }

    #[inline]
    pub fn notify_one(&self) {
        // No-op
    }

    #[inline]
    pub fn notify_all(&self) {
        // No-op
    }

    #[inline]
    pub fn wait(&self, mutex: &Mutex) {
        panic!("deadlock: single-threaded program is waiting on a condvar");
    }

    #[inline]
    pub fn wait_timeout(&self, mutex: &Mutex, dur: Duration) -> bool {
        // Pretend to have timed out, as there's no other way to end a wait.
        false
    }

    #[inline]
    pub fn destroy(&self) {
        // No-op
    }
}
