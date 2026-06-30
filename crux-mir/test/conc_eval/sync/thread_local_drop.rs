use std::cell::RefCell;

thread_local! {
    static X: RefCell<Vec<i32>> = RefCell::new(vec![1, 2, 3]);
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    X.with_borrow_mut(|x| x.push(4));
    X.with_borrow(|x| x.iter().copied().sum::<i32>())
}

pub fn main() {
    println!("{:?}", crux_test());
}
