use crate::sync::atomic::Ordering;

#[cfg(test)]
use stdarch_test::assert_instr;

/// Compares and exchange 16 bytes (128 bits) of data atomically.
///
/// This intrinsic corresponds to the `cmpxchg16b` instruction on `x86_64`
/// processors. It performs an atomic compare-and-swap, updating the `ptr`
/// memory location to `val` if the current value in memory equals `old`.
///
/// # Return value
///
/// This function returns the previous value at the memory location. If it is
/// equal to `old` then the memory was updated to `new`.
///
/// # Memory Orderings
///
/// This atomic operations has the same semantics of memory orderings as
/// `AtomicUsize::compare_exchange` does, only operating on 16 bytes of memory
/// instead of just a pointer.
///
/// For more information on memory orderings here see the `compare_exchange`
/// documentation for other `Atomic*` types in the standard library.
///
/// # Unsafety
///
/// This method is unsafe because it takes a raw pointer and will attempt to
/// read and possibly write the memory at the pointer. The pointer must also be
/// aligned on a 16-byte boundary.
///
/// This method also requires the `cmpxchg16b` CPU feature to be available at
/// runtime to work correctly. If the CPU running the binary does not actually
/// support `cmpxchg16b` and the program enters an execution path that
/// eventually would reach this function the behavior is undefined.
///
/// The failure ordering must be [`Ordering::SeqCst`], [`Ordering::Acquire`] or
/// [`Ordering::Relaxed`], or this function call is undefined. See the `Atomic*`
/// documentation's `compare_exchange` function for more information. When
/// `compare_exchange` panics, this is undefined behavior. Currently this
/// function aborts the process with an undefined instruction.
#[inline]
#[cfg_attr(test, assert_instr(cmpxchg16b, success = Ordering::SeqCst, failure = Ordering::SeqCst))]
#[target_feature(enable = "cmpxchg16b")]
pub unsafe fn cmpxchg16b(
    dst: *mut u128,
    old: u128,
    new: u128,
    success: Ordering,
    failure: Ordering,
) -> u128 {
    use crate::{intrinsics, sync::atomic::Ordering::*};

    debug_assert!(dst as usize % 16 == 0);

    let (val, _ok) = match (success, failure) {
        (Relaxed, Relaxed) => intrinsics::atomic_cxchg_relaxed_relaxed(dst, old, new),
        (Relaxed, Acquire) => intrinsics::atomic_cxchg_relaxed_acquire(dst, old, new),
        (Relaxed, SeqCst) => intrinsics::atomic_cxchg_relaxed_seqcst(dst, old, new),
        (Acquire, Relaxed) => intrinsics::atomic_cxchg_acquire_relaxed(dst, old, new),
        (Acquire, Acquire) => intrinsics::atomic_cxchg_acquire_acquire(dst, old, new),
        (Acquire, SeqCst) => intrinsics::atomic_cxchg_acquire_seqcst(dst, old, new),
        (Release, Relaxed) => intrinsics::atomic_cxchg_release_relaxed(dst, old, new),
        (Release, Acquire) => intrinsics::atomic_cxchg_release_acquire(dst, old, new),
        (Release, SeqCst) => intrinsics::atomic_cxchg_release_seqcst(dst, old, new),
        (AcqRel, Relaxed) => intrinsics::atomic_cxchg_acqrel_relaxed(dst, old, new),
        (AcqRel, Acquire) => intrinsics::atomic_cxchg_acqrel_acquire(dst, old, new),
        (AcqRel, SeqCst) => intrinsics::atomic_cxchg_acqrel_seqcst(dst, old, new),
        (SeqCst, Relaxed) => intrinsics::atomic_cxchg_seqcst_relaxed(dst, old, new),
        (SeqCst, Acquire) => intrinsics::atomic_cxchg_seqcst_acquire(dst, old, new),
        (SeqCst, SeqCst) => intrinsics::atomic_cxchg_seqcst_seqcst(dst, old, new),

        // The above block is all copied from libcore, and this statement is
        // also copied from libcore except that it's a panic in libcore and we
        // have a little bit more of a lightweight panic here.
        _ => crate::core_arch::x86::ud2(),
    };
    val
}
