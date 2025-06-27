use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let array = Cell::new([0; 5]);
    let slice = (&array as &Cell<[_]>).as_slice_of_cells();
    slice[3].set(3);
    slice[1].set(1);
    array.get()[1] + array.get()[3]
}

pub fn main() {
    println!("{:?}", crux_test());
}
