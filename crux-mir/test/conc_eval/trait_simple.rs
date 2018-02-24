#[cfg(with_main)]
fn main() {
   let d = Data(32);
   println!("{}", fun(&d));
}

struct Data(u32);

trait Foo {
    fn foo (&self) -> u32;
}

impl Foo for Data {
    fn foo (&self) -> u32 {
        return 1;
    }
}


fn fun(f: &Foo) -> () {
   f.foo();
}
