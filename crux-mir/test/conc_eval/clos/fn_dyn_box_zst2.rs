// Test calling `Box<dyn FnOnce>` where the closure type is nonempty but still zero-sized.
use std::marker::PhantomData;

fn call_closure_box(f: Box<dyn FnOnce(i32, i32) -> i32>) -> i32 {
    f(1, 2)
}

struct Token<'a>(PhantomData<&'a ()>);
impl<'a> Token<'a> {
    pub fn new() -> Token<'static> {
        Token(PhantomData)
    }

    pub fn f(&self, x: &'a i32) -> i32 {
        *x + 1
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let token = Token::new();
    call_closure_box(Box::new(move |x, y| x + token.f(&y)))
}

pub fn main() {
    println!("{:?}", crux_test());
}
