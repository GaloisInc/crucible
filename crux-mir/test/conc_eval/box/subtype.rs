// This test case exists to ensure that crucible-mir supports simulating the
// `Subtype` `PlaceElem`. The code here is a stripped-down version of this
// `rustc` test case:
// https://github.com/rust-lang/rust/blob/3148e6a9933b17b28ed6c7b8d8bd6c8e49fe4a50/tests/mir-opt/mir_subtyping.rs

struct Foo<T: 'static>(T);

fn useful<'a>(x: &'a u8) -> &'a u8 {
    x
}

struct Wrapper(for<'b> fn(&'b u8) -> &'b u8);

static X: u8 = 42;

#[cfg_attr(crux, crux::test)]
pub fn crux_test() -> u8 {
    let wrapper = Wrapper(useful);
    let hr_fnptr = Box::new(Foo::<for<'a> fn(&'a u8) -> &'a u8>(wrapper.0));
    let lr_fnptr = hr_fnptr as Box<Foo<fn(&'static u8) -> &'static u8>>; // This line requires a Subtype
    *((*lr_fnptr).0)(&X)
}

pub fn main() {
    println!("{:?}", crux_test());
}
