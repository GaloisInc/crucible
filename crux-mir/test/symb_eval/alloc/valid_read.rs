extern crate crucible;
use crucible::*;
use crucible::alloc::allocate;

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    unsafe {
        let ptr = allocate::<i32>(10);
        for i in 0..10 {
            *ptr.offset(i) = i as i32;
        }
        let mut sum = 0;
        for i in 0..10 {
            sum += *ptr.offset(i);
        }
        assert!(sum == 45);
        sum
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}

