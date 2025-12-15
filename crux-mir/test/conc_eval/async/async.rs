// FAIL: crux-mir does not support async yet (#1369)

use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, RawWaker, RawWakerVTable, Waker};

async fn f() -> u32 { 42 }

// Minimal waker; OK since `f()` is immediately Ready (no .await inside).
fn dummy_waker() -> Waker {
    unsafe fn clone(_: *const ()) -> RawWaker { RawWaker::new(std::ptr::null(), &VTABLE) }
    unsafe fn wake(_: *const ()) {}
    unsafe fn wake_by_ref(_: *const ()) {}
    unsafe fn drop(_: *const ()) {}
    static VTABLE: RawWakerVTable = RawWakerVTable::new(clone, wake, wake_by_ref, drop);
    unsafe { Waker::from_raw(RawWaker::new(std::ptr::null(), &VTABLE)) }
}

fn block_on<F: Future>(mut fut: F) -> F::Output {
    let waker = dummy_waker();
    let mut cx = Context::from_waker(&waker);
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    match fut.as_mut().poll(&mut cx) {
        Poll::Ready(x) => x,
        Poll::Pending => panic!("unexpected Pending"),
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    block_on(f())
}

fn main() {
    println!("{}", crux_test());
}
