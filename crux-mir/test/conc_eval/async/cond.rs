use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

async fn f() -> u32 {
    let x = if g(0).await > 0 {
        g(1).await
    } else {
        g(2).await
    };
    let y = g(3).await;
    x + y
}

async fn g(x: u32) -> u32 { x + 1 }

fn block_on<F: Future>(mut fut: F) -> F::Output {
    let mut cx = Context::from_waker(Waker::noop());
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
