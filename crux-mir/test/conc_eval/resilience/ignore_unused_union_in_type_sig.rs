#[repr(C)]
union MyUnion {
    f1: u32,
    f2: f32,
}

fn f() -> MyUnion {
    MyUnion { f1: 1 }
}

fn g(x: bool) -> u32 {
    if x {
        unsafe { f().f1 }
    } else {
        2
    }
}

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u32 {
    g(false)
}

pub fn main() {
    println!("{:?}", crux_test());
}
