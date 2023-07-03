#![stable(feature = "futures_api", since = "1.36.0")]

//! Asynchronous basic functionality.
//!
//! Please see the fundamental [`async`] and [`await`] keywords and the [async book]
//! for more information on asynchronous programming in Rust.
//!
//! [`async`]: ../../std/keyword.async.html
//! [`await`]: ../../std/keyword.await.html
//! [async book]: https://rust-lang.github.io/async-book/

use crate::ptr::NonNull;
use crate::task::Context;

mod future;
mod into_future;
mod join;
mod pending;
mod poll_fn;
mod ready;

#[stable(feature = "futures_api", since = "1.36.0")]
pub use self::future::Future;

#[unstable(feature = "future_join", issue = "91642")]
pub use self::join::join;

#[stable(feature = "into_future", since = "1.64.0")]
pub use into_future::IntoFuture;

#[stable(feature = "future_readiness_fns", since = "1.48.0")]
pub use pending::{pending, Pending};
#[stable(feature = "future_readiness_fns", since = "1.48.0")]
pub use ready::{ready, Ready};

#[stable(feature = "future_poll_fn", since = "1.64.0")]
pub use poll_fn::{poll_fn, PollFn};

/// This type is needed because:
///
/// a) Generators cannot implement `for<'a, 'b> Generator<&'a mut Context<'b>>`, so we need to pass
///    a raw pointer (see <https://github.com/rust-lang/rust/issues/68923>).
/// b) Raw pointers and `NonNull` aren't `Send` or `Sync`, so that would make every single future
///    non-Send/Sync as well, and we don't want that.
///
/// It also simplifies the HIR lowering of `.await`.
#[lang = "ResumeTy"]
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[derive(Debug, Copy, Clone)]
pub struct ResumeTy(NonNull<Context<'static>>);

#[unstable(feature = "gen_future", issue = "50547")]
unsafe impl Send for ResumeTy {}

#[unstable(feature = "gen_future", issue = "50547")]
unsafe impl Sync for ResumeTy {}

/// Wrap a generator in a future.
///
/// This function returns a `GenFuture` underneath, but hides it in `impl Trait` to give
/// better error messages (`impl Future` rather than `GenFuture<[closure.....]>`).
// This is `const` to avoid extra errors after we recover from `const async fn`
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[rustc_const_unstable(feature = "gen_future", issue = "50547")]
#[inline]
pub const fn from_generator<T>(gen: T) -> impl Future<Output = T::Return>
where
    T: crate::ops::Generator<ResumeTy, Yield = ()>,
{
    use crate::{
        ops::{Generator, GeneratorState},
        pin::Pin,
        task::Poll,
    };

    #[rustc_diagnostic_item = "gen_future"]
    struct GenFuture<T: Generator<ResumeTy, Yield = ()>>(T);

    // We rely on the fact that async/await futures are immovable in order to create
    // self-referential borrows in the underlying generator.
    impl<T: Generator<ResumeTy, Yield = ()>> !Unpin for GenFuture<T> {}

    impl<T: Generator<ResumeTy, Yield = ()>> Future for GenFuture<T> {
        type Output = T::Return;
        #[track_caller]
        fn poll(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<Self::Output> {
            // SAFETY: Safe because we're !Unpin + !Drop, and this is just a field projection.
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

#[lang = "get_context"]
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[must_use]
#[inline]
pub unsafe fn get_context<'a, 'b>(cx: ResumeTy) -> &'a mut Context<'b> {
    // SAFETY: the caller must guarantee that `cx.0` is a valid pointer
    // that fulfills all the requirements for a mutable reference.
    unsafe { &mut *cx.0.as_ptr().cast() }
}

// FIXME(swatinem): This fn is currently needed to work around shortcomings
// in type and lifetime inference.
// See the comment at the bottom of `LoweringContext::make_async_expr` and
// <https://github.com/rust-lang/rust/issues/104826>.
#[doc(hidden)]
#[unstable(feature = "gen_future", issue = "50547")]
#[inline]
#[lang = "identity_future"]
pub const fn identity_future<O, Fut: Future<Output = O>>(f: Fut) -> Fut {
    f
}
