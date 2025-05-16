
fn ret1() -> i32 { 1 }
fn ret2() -> i32 { 2 }

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let a = true.then(|| 10);
    let b = false.then(|| 20);
    let c = true.then(ret1);
    let d = false.then(ret2);
    a.unwrap_or(0) + b.unwrap_or(0) + c.unwrap_or(0) + d.unwrap_or(0)
}

pub fn main() {
    println!("{:?}", crux_test());
}
