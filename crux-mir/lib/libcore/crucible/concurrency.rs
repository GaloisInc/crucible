//! Crucible concurrency intrinsics


// Signal a possible preemption point. `ro` is true if this
// preemption point MUST be read only. It is always safe to
// pass `false`.
#[unstable(feature = "crucible_intrinsics", issue = "none")]
pub fn sched_yield<T>(ro: bool, x: T) {}

// Signal a lock acquisition. Modeling this inside Crucible
// is more efficient than on top of lower level primitives.
#[unstable(feature = "crucible_intrinsics", issue = "none")]
pub fn mutex_lock<T>(x: T) {}

// Signal a lock release. Modeling this inside Crucible
// is more efficient than on top of lower level primitives.
#[unstable(feature = "crucible_intrinsics", issue = "none")]
pub fn mutex_unlock<T>(x: T) {}

// Signal to block until thread `thid` has terminated.
pub fn join<T>(thid : u64) -> T {
    panic!("crucible::concurrency::join should never be executed!")
}

fn thread_exit<T>(f:T) {}

/**
Funny game we're playing here:

In the caller of "spawn", we'll actually effectively overide the behavior of
this function and return the ID of the new thread, while at the same time
running the body of this function (and f) in a new thread.

The main reason for this is that MIR appears to do a lot of inlining (or perhaps
it's just specialization?) to arrive at the monomorphic spawn call.
So the first thing that worked was just to spawn the 'internal' function.

This means that the spawned thread will actually want to return 0 after 'f'
returns. So instead we'll just explicitly call a function that indicates what
the returned value was, from which we can yield control & mark the thread done
(effectively never running the return handler for the thread in crucible land).
*/
fn spawn_internal<F, T>(f: F) -> u32
where
    F: FnOnce() -> T,
    F: Send + 'static,
    T: Send + 'static,
{
    let x = f();
    thread_exit(x);
    0 // Will override
}

#[stable(feature = "rust1", since = "1.0.0")]
pub fn spawn<F, T>(f: F) -> u32
where
    F: FnOnce() -> T,
    F: Send + 'static,
    T: Send + 'static,
{
    spawn_internal(f)
}
