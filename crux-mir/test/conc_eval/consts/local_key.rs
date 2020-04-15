#![cfg_attr(not(with_main), no_std)]

struct LocalKey {
    fn_ptr: fn() -> i32,
}

impl LocalKey {
    fn get(&self) -> i32 {
        (self.fn_ptr)()
    }
}

fn f() -> i32 { 1 }
fn g() -> i32 { 2 }

const LOCAL_KEY: LocalKey = LocalKey { fn_ptr: f };

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", LOCAL_KEY.get());
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux_test)] fn crux_test() -> i32 { LOCAL_KEY.get() }
