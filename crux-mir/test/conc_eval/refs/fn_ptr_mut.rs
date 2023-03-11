#![feature(never_type)]

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let x: Result<i32, fn()> = Ok(1);
    match x {
        Ok(x) => x,
        Err(mut e) => {
            let r = &mut e;
            panic!();
        },
    }
}

pub fn main() {
    println!("{:?}", crux_test());
}
