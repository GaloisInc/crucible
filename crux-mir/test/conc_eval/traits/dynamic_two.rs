// example of a rust program with two different traits
// currently, mir-json does *not* produce info about both

struct Data(u32);

trait Bar {
    fn bar (&self) -> u32;
}


trait Foo {
    fn foo (&self) -> u32;
}


impl Foo for Data {
    fn foo (&self) -> u32 {
        return self.bar()
    }
}

impl Bar for Data {
    fn bar (&self) -> u32 {
        return 1;
    }
}



fn fun(f: &Foo) -> u32 {
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
