#![cfg_attr(not(with_main), feature(custom_attribute))]
#![cfg_attr(not(with_main), no_std)]
struct BI {
    i: [[i32; 4]; 2],
}

#[inline(never)]
#[no_mangle]
fn ff (w: &mut BI) {
    for row in w.i.iter_mut() {
        for col in row.iter_mut() {
            *col = 0;
        }
    }
}

fn f(_:()) {
    let x = &mut BI{i: [[0 as i32; 4]; 2]};
    ff(x);
    x.i[1][3];
}


const ARG: () = ();

#[cfg(with_main)]
pub fn main() {
   println!("{:?}", f(ARG));
}
#[cfg(not(with_main))] #[crux_test] fn crux_test() -> () { f(ARG) }
