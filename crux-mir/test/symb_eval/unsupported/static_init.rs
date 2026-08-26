pub union Mix {
    f1: (bool, u8),
    f2: (u8, bool),
}

// Z0 has a value which is half from one of the union and half from the other
pub static Z0: Mix = {
    let mut u = Mix { f1: (true, 99) };
    u.f2.0 = 99; // overwrite through *the other* union variant, but only half the value
    u
};

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> (u8, bool) {
    unsafe { Z0.f2 }
}

pub fn main() {
    println!("{:?}", crux_test());
}
