#![feature(bound_cloned)]
#![feature(box_syntax)]
#![feature(cell_update)]
#![feature(core_private_bignum)]
#![feature(core_private_diy_float)]
#![feature(debug_map_key_value)]
#![feature(dec2flt)]
#![feature(exact_size_is_empty)]
#![feature(fixed_size_array)]
#![feature(flt2dec)]
#![feature(fmt_internals)]
#![feature(hashmap_internals)]
#![feature(is_sorted)]
#![feature(iter_once_with)]
#![feature(pattern)]
#![feature(range_is_empty)]
#![feature(raw)]
#![feature(saturating_neg)]
#![feature(slice_patterns)]
#![feature(sort_internals)]
#![feature(slice_partition_at_index)]
#![feature(specialization)]
#![feature(step_trait)]
#![feature(str_internals)]
#![feature(test)]
#![feature(trusted_len)]
#![feature(try_trait)]
#![feature(inner_deref)]
#![feature(slice_internals)]
#![feature(slice_partition_dedup)]
#![feature(int_error_matching)]
#![feature(const_fn)]
#![feature(iter_partition_in_place)]
#![feature(iter_is_partitioned)]

extern crate test;

mod alloc;
mod any;
mod array;
mod ascii;
mod atomic;
mod cell;
mod char;
mod clone;
mod cmp;
mod fmt;
mod hash;
mod intrinsics;
mod iter;
mod manually_drop;
mod mem;
mod nonzero;
mod num;
mod ops;
mod option;
mod pattern;
mod ptr;
mod result;
mod slice;
mod str;
mod str_lossy;
mod time;
mod tuple;
