use std::future::Future;
use std::pin::Pin;
use std::task::{Context, Poll, Waker};

async fn f() -> u32 {
    let g = async |x: u32| x + 1;
    let a = g(1).await;
    let b = g(2).await;
    a + b
}

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
