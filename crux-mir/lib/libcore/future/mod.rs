#![stable(feature = "futures_api", since = "1.36.0")]

//! Asynchronous values.

#[cfg(not(bootstrap))]
use crate::{
    ops::{Generator, GeneratorState},
    pin::Pin,
    ptr::NonNull,
    task::{Context, Poll},
};

mod future;
#[stable(feature = "futures_api", since = "1.36.0")]
pub use self::future::Future;

/// This type is needed because:
///
/// a) Generators cannot implement `for<'a, 'b> Generator<&'a mut Context<'b>>`, so we need to pass
///    a raw pointer (see https://github.com/rust-lang/rust/issues/68923).
/// b) Raw pointers and `NonNull` aren't `Send` or `Sync`, so that would make every single future
///    non-Send/Sync as well, and we don't want that.
///
/// It also simplifies the HIR lowering of `.await`.
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[cfg(not(bootstrap))]
#[derive(Debug, Copy, Clone)]
pub struct ResumeTy(NonNull<Context<'static>>);

#[unstable(feature = "gen_future", issue = "50547")]
#[cfg(not(bootstrap))]
unsafe impl Send for ResumeTy {}

#[unstable(feature = "gen_future", issue = "50547")]
#[cfg(not(bootstrap))]
unsafe impl Sync for ResumeTy {}

/// Wrap a generator in a future.
///
/// This function returns a `GenFuture` underneath, but hides it in `impl Trait` to give
/// better error messages (`impl Future` rather than `GenFuture<[closure.....]>`).
// This is `const` to avoid extra errors after we recover from `const async fn`
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[cfg(not(bootstrap))]
#[inline]
pub const fn from_generator<T>(gen: T) -> impl Future<Output = T::Return>
where
    T: Generator<ResumeTy, Yield = ()>,
{
    struct GenFuture<T: Generator<ResumeTy, Yield = ()>>(T);

    // We rely on the fact that async/await futures are immovable in order to create
    // self-referential borrows in the underlying generator.
    impl<T: Generator<ResumeTy, Yield = ()>> !Unpin for GenFuture<T> {}

    impl<T: Generator<ResumeTy, Yield = ()>> Future for GenFuture<T> {
        type Output = T::Return;
        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            // Safety: Safe because we're !Unpin + !Drop, and this is just a field projection.
            let gen = unsafe { Pin::map_unchecked_mut(self, |s| &mut s.0) };

            // Resume the generator, turning the `&mut Context` into a `NonNull` raw pointer. The
            // `.await` lowering will safely cast that back to a `&mut Context`.
            match gen.resume(ResumeTy(NonNull::from(cx).cast::<Context<'static>>())) {
                GeneratorState::Yielded(()) => Poll::Pending,
                GeneratorState::Complete(x) => Poll::Ready(x),
            }
        }
    }

    GenFuture(gen)
}

#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[cfg(not(bootstrap))]
#[inline]
pub unsafe fn poll_with_context<F>(f: Pin<&mut F>, mut cx: ResumeTy) -> Poll<F::Output>
where
    F: Future,
{
    F::poll(f, cx.0.as_mut())
}
