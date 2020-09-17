#![feature(never_type)]

#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let x: Result<i32, fn()> = Ok(1);
    match x {
        Ok(x) => x,
        Err(e) => {
            let r = &e;
            panic!();
        },
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
