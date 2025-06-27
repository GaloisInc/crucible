use std::cell::Cell;

#[cfg_attr(crux, crux::test)]
fn crux_test() -> i32 {
    let mut array = [0; 5];
    let slice = &mut array as &mut [_];
    let cell = Cell::from_mut(slice);
    let slice = cell.as_slice_of_cells();
    slice[3].set(3);
    slice[1].set(1);
    array[1] + array[3]
}

pub fn main() {
    println!("{:?}", crux_test());
}
