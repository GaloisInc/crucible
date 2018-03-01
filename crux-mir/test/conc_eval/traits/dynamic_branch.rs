struct Data(u32);

trait Foo {
    fn foo (&self) -> u32;
}

impl Foo for Data {
    fn foo (&self) -> u32 {
        return 1;
    }
}

impl Foo for String {
    fn foo (&self) -> u32 {
        return 2;
    }
}


fn fun(f: &Foo) -> u32 {
   return f.foo();
}

fn f(_: ()) -> u32 {
    let d = Data(32);
    let s = String::from("hello");
    if true {
        fun(&d)
    } else {
        fun(&s)
    }
}

const ARG: () = ();

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG));
}
