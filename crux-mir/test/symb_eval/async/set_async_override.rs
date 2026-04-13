extern crate crucible;

use crucible::set_async_override;
use crucible::{Symbolic, crucible_assert, override_};
use crucible::coroutine::trivial_block_on;

async fn get_random(_x: u32) -> u32 {
    panic!("This should have been overridden in this test");
}

async fn add_two_random() -> u32 {
    let x = get_random(5).await;
    let y = get_random(6).await;
    x + y
}

#[crux::test]
fn test_get_random() {
    set_async_override!(get_random, |limit: u32| -> u32 {
        Symbolic::symbolic_where("random", |&x| x < limit)
    });
    crucible_assert!(trivial_block_on(add_two_random()) < 10);
}
