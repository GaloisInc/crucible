use crate::fmt;
use crate::marker;
use crate::ops::Deref;
use crate::sys_common::poison::{self, TryLockError, TryLockResult, LockResult};
use crate::sys::mutex as sys;
use crate::panic::{UnwindSafe, RefUnwindSafe};

/// A re-entrant mutual exclusion
///
/// This mutex will block *other* threads waiting for the lock to become
/// available. The thread which has already locked the mutex can lock it
/// multiple times without blocking, preventing a common source of deadlocks.
pub struct ReentrantMutex<T> {
    inner: Box<sys::ReentrantMutex>,
    poison: poison::Flag,
    data: T,
}

unsafe impl<T: Send> Send for ReentrantMutex<T> {}
unsafe impl<T: Send> Sync for ReentrantMutex<T> {}

impl<T> UnwindSafe for ReentrantMutex<T> {}
impl<T> RefUnwindSafe for ReentrantMutex<T> {}


/// An RAII implementation of a "scoped lock" of a mutex. When this structure is
/// dropped (falls out of scope), the lock will be unlocked.
///
/// The data protected by the mutex can be accessed through this guard via its
/// Deref implementation.
///
/// # Mutability
///
/// Unlike `MutexGuard`, `ReentrantMutexGuard` does not implement `DerefMut`,
/// because implementation of the trait would violate Rust’s reference aliasing
/// rules. Use interior mutability (usually `RefCell`) in order to mutate the
/// guarded data.
#[must_use = "if unused the ReentrantMutex will immediately unlock"]
pub struct ReentrantMutexGuard<'a, T: 'a> {
    // funny underscores due to how Deref currently works (it disregards field
    // privacy).
    __lock: &'a ReentrantMutex<T>,
    __poison: poison::Guard,
}

impl<T> !marker::Send for ReentrantMutexGuard<'_, T> {}


impl<T> ReentrantMutex<T> {
    /// Creates a new reentrant mutex in an unlocked state.
    pub fn new(t: T) -> ReentrantMutex<T> {
        unsafe {
            let mut mutex = ReentrantMutex {
                inner: box sys::ReentrantMutex::uninitialized(),
                poison: poison::Flag::new(),
                data: t,
            };
            mutex.inner.init();
            mutex
        }
    }

    /// Acquires a mutex, blocking the current thread until it is able to do so.
    ///
    /// This function will block the caller until it is available to acquire the mutex.
    /// Upon returning, the thread is the only thread with the mutex held. When the thread
    /// calling this method already holds the lock, the call shall succeed without
    /// blocking.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return failure if the mutex would otherwise be
    /// acquired.
    pub fn lock(&self) -> LockResult<ReentrantMutexGuard<'_, T>> {
        unsafe { self.inner.lock() }
        ReentrantMutexGuard::new(&self)
    }

    /// Attempts to acquire this lock.
    ///
    /// If the lock could not be acquired at this time, then `Err` is returned.
    /// Otherwise, an RAII guard is returned.
    ///
    /// This function does not block.
    ///
    /// # Errors
    ///
    /// If another user of this mutex panicked while holding the mutex, then
    /// this call will return failure if the mutex would otherwise be
    /// acquired.
    pub fn try_lock(&self) -> TryLockResult<ReentrantMutexGuard<'_, T>> {
        if unsafe { self.inner.try_lock() } {
            Ok(ReentrantMutexGuard::new(&self)?)
        } else {
            Err(TryLockError::WouldBlock)
        }
    }
}

impl<T> Drop for ReentrantMutex<T> {
    fn drop(&mut self) {
        // This is actually safe b/c we know that there is no further usage of
        // this mutex (it's up to the user to arrange for a mutex to get
        // dropped, that's not our job)
        unsafe { self.inner.destroy() }
    }
}

impl<T: fmt::Debug + 'static> fmt::Debug for ReentrantMutex<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.try_lock() {
            Ok(guard) => f.debug_struct("ReentrantMutex").field("data", &*guard).finish(),
            Err(TryLockError::Poisoned(err)) => {
                f.debug_struct("ReentrantMutex").field("data", &**err.get_ref()).finish()
            },
            Err(TryLockError::WouldBlock) => {
                struct LockedPlaceholder;
                impl fmt::Debug for LockedPlaceholder {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                        f.write_str("<locked>")
                    }
                }

                f.debug_struct("ReentrantMutex").field("data", &LockedPlaceholder).finish()
            }
        }
    }
}

impl<'mutex, T> ReentrantMutexGuard<'mutex, T> {
    fn new(lock: &'mutex ReentrantMutex<T>)
            -> LockResult<ReentrantMutexGuard<'mutex, T>> {
        poison::map_result(lock.poison.borrow(), |guard| {
            ReentrantMutexGuard {
                __lock: lock,
                __poison: guard,
            }
        })
    }
}

impl<T> Deref for ReentrantMutexGuard<'_, T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.__lock.data
    }
}

impl<T> Drop for ReentrantMutexGuard<'_, T> {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            self.__lock.poison.done(&self.__poison);
            self.__lock.inner.unlock();
        }
    }
}


#[cfg(all(test, not(target_os = "emscripten")))]
mod tests {
    use crate::sys_common::remutex::{ReentrantMutex, ReentrantMutexGuard};
    use crate::cell::RefCell;
    use crate::sync::Arc;
    use crate::thread;

    #[test]
    fn smoke() {
        let m = ReentrantMutex::new(());
        {
            let a = m.lock().unwrap();
            {
                let b = m.lock().unwrap();
                {
                    let c = m.lock().unwrap();
                    assert_eq!(*c, ());
                }
                assert_eq!(*b, ());
            }
            assert_eq!(*a, ());
        }
    }

    #[test]
    fn is_mutex() {
        let m = Arc::new(ReentrantMutex::new(RefCell::new(0)));
        let m2 = m.clone();
        let lock = m.lock().unwrap();
        let child = thread::spawn(move || {
            let lock = m2.lock().unwrap();
            assert_eq!(*lock.borrow(), 4950);
        });
        for i in 0..100 {
            let lock = m.lock().unwrap();
            *lock.borrow_mut() += i;
        }
        drop(lock);
        child.join().unwrap();
    }

    #[test]
    fn trylock_works() {
        let m = Arc::new(ReentrantMutex::new(()));
        let m2 = m.clone();
        let _lock = m.try_lock().unwrap();
        let _lock2 = m.try_lock().unwrap();
        thread::spawn(move || {
            let lock = m2.try_lock();
            assert!(lock.is_err());
        }).join().unwrap();
        let _lock3 = m.try_lock().unwrap();
    }

    pub struct Answer<'a>(pub ReentrantMutexGuard<'a, RefCell<u32>>);
    impl Drop for Answer<'_> {
        fn drop(&mut self) {
            *self.0.borrow_mut() = 42;
        }
    }

    #[test]
    fn poison_works() {
        let m = Arc::new(ReentrantMutex::new(RefCell::new(0)));
        let mc = m.clone();
        let result = thread::spawn(move ||{
            let lock = mc.lock().unwrap();
            *lock.borrow_mut() = 1;
            let lock2 = mc.lock().unwrap();
            *lock.borrow_mut() = 2;
            let _answer = Answer(lock2);
            panic!("What the answer to my lifetimes dilemma is?");
        }).join();
        assert!(result.is_err());
        let r = m.lock().err().unwrap().into_inner();
        assert_eq!(*r.borrow(), 42);
    }
}
