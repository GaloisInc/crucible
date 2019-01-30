// FAIL: user error (JSON Decoding of MIR failed: Error in $.fns[2].body.blocks[0].block.data[0].rhs.usevar.data.literal: Don't know how to parse Text 'a' into a Char)

fn g () -> char {
    'a'
}

fn h () -> () {
    ()
}

fn f (x : i32) -> () {
    h ();
}

const ARG : i32 = 0;

#[cfg(with_main)]
fn main() {
    println!("{:?}", f(ARG))
}
