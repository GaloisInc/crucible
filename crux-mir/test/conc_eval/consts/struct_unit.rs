#[derive(Debug)]
struct Foo {
    x: (),
}

#[cfg_attr(crux, crux::test)]
fn crux_test() -> Result<(), Foo> {
    //None.ok_or(Foo { x: () })?;
    //Ok(())
    Err(Foo { x: () })
}

pub fn main() {
    println!("{:?}", crux_test());
}
