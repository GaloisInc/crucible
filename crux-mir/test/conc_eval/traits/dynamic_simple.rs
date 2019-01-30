// FAIL: dynamic trait object

struct Data(u32);

trait Foo {
    fn foo (&self) -> u32;
}

impl Foo for Data {
    fn foo (&self) -> u32 {
        return 1;
    }
}


fn fun(f: &dyn Foo) -> u32 {
   f.foo()
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    fun(&d)
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
   println!("{:?}", f(ARG));
}
