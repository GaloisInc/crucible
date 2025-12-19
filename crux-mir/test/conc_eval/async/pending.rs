use std::future::{self, Future};
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

fn pend(i: u32) -> impl Future<Output = u32> {
    let mut j = 0;
    future::poll_fn(move |_cx| {
        if j >= i {
            Poll::Ready(i)
        } else {
            j += 1;
            Poll::Pending
        }
    })
}

async fn f() -> u32 {
    let a = pend(0).await;
    let b = pend(1).await;
    let c = pend(2).await;
    a + b + c
}

fn block_on<F: Future>(mut fut: F) -> F::Output {
    let mut cx = Context::from_waker(Waker::noop());
    let mut fut = unsafe { Pin::new_unchecked(&mut fut) };
    loop {
        match fut.as_mut().poll(&mut cx) {
            Poll::Ready(x) => return x,
            Poll::Pending => {},
        }
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> u32 {
    block_on(f())
}

fn main() {
    println!("{}", crux_test());
}
