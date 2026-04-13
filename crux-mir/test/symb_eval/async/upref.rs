extern crate crucible;

use crucible::{Symbolic, crucible_assert, override_};
use crucible::coroutine::{coroutine_field_ref, trivial_block_on};
use std::pin::Pin;
use std::task::{Context, Poll, Waker};
use std::future::Future;

async fn get_random(x: u32) -> u32 {
    panic!("This should have been overridden in this test");
}

async fn add_two_random() -> u32 {
    let x = get_random(5).await;
    let y = get_random(6).await;
    x + y
}

fn get_random_override<F>(fut: Pin<&mut F>, cx: &mut Context) -> Poll<F::Output>
where
    F: Future<Output = u32>,
{
    let limit: u32 = *coroutine_field_ref::<_, _, 0>(&*fut);
    let x = Symbolic::symbolic_where("random", |&x| x < limit);
    Poll::Ready(x)
}

fn override_random_poll<F: Future<Output = u32>>(_: F) {
    override_(F::poll, get_random_override::<F>);
}

#[crux::test]
fn test_get_random() {
    override_random_poll(get_random(0));
    crucible_assert!(trivial_block_on(add_two_random()) < 10);
}
