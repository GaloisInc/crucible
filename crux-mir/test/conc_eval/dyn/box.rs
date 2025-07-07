//! Test introduction and dropping of `Box<dyn Trait>`.

trait Foo {}

impl Foo for usize {}

struct DropType(u32, u32);

impl Foo for DropType {}

static mut DROPPED: bool = false;

impl Drop for DropType {
    fn drop(&mut self) {
        unsafe {
            DROPPED = true;
        }
    }
}

#[cfg_attr(crux, crux::test)]
fn crux_test() {
    let x: Box<dyn Foo> = Box::new(3usize);
    let y: Box<dyn Foo> = Box::new(DropType(3, 4));
    drop(y);
    assert!(unsafe { DROPPED });
}

fn main() {
    println!("{:?}", crux_test());
}
