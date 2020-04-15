pub trait Foo {
    fn foo(&self) -> i32;
}

pub trait Bar: Foo {
    fn bar(&self) -> i32;
}

impl Foo for () {
    fn foo(&self) -> i32 { 1 }
}

impl Bar for () {
    fn bar(&self) -> i32 { 2 }
}


#[cfg_attr(crux, crux_test)]
fn crux_test() -> i32 {
    let x = &() as &dyn Bar;
    let y = &() as &dyn Foo;
    x.bar() + x.foo() + y.foo()
}

pub fn main() {
    println!("{:?}", crux_test());
}
