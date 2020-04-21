// Original implementation taken from rust-memchr.
// Copyright 2015 Andrew Gallant, bluss and Nicolas Koch

pub fn memchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    let p = unsafe {
        libc::memchr(
            haystack.as_ptr() as *const libc::c_void,
            needle as libc::c_int,
            haystack.len(),
        )
    };
    if p.is_null() { None } else { Some(p as usize - (haystack.as_ptr() as usize)) }
}

pub fn memrchr(needle: u8, haystack: &[u8]) -> Option<usize> {
    fn memrchr_specific(needle: u8, haystack: &[u8]) -> Option<usize> {
        core::slice::memchr::memrchr(needle, haystack)
    }

    memrchr_specific(needle, haystack)
}
