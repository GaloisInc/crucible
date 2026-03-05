#![cfg_attr(not(with_main), no_std)]
fn f(x: bool) -> bool {
    x ^ true
}

fn ord_ops() {
    assert!(false < true);
    assert!(!(true < true));
    assert!(!(false < false));
    assert!(!(true < false));
    
    assert!(false <= true);
    assert!(true <= true);
    assert!(false <= false);
    assert!(!(true <= false));

    assert!(!(false > true));
    assert!(!(true > true));
    assert!(!(false > false));
    assert!(true > false);
    
    assert!(!(false >= true));
    assert!(true >= true);
    assert!(false >= false);
    assert!(true >= false);
}

const ARG: bool = true;

#[cfg(with_main)]
pub fn main() {
    println!("{:?}", f(ARG));
    ord_ops();
}
#[cfg(not(with_main))] #[cfg_attr(crux, crux::test)] fn crux_test() -> bool { f(ARG) }
