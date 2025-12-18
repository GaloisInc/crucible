#![feature(coroutines, coroutine_trait, stmt_expr_attributes)]

use std::ops::{Coroutine, CoroutineState};
use std::pin::Pin;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> (i32, usize) {
    let mut coroutine = #[coroutine] || {
        yield 1;
        return "foo"
    };

    let mut p = Pin::new(&mut coroutine);
    let x = match p.as_mut().resume(()) {
        CoroutineState::Yielded(x) => x,
        CoroutineState::Complete(_) => panic!(),
    };
    let y = match p.as_mut().resume(()) {
        CoroutineState::Yielded(_) => panic!(),
        CoroutineState::Complete(y) => y,
    };
    (x, y.len())
}

fn main() {
    println!("{:?}", crux_test());
}
