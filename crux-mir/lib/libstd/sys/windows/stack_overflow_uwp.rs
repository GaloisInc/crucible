#![cfg_attr(test, allow(dead_code))]

pub struct Handler;

impl Handler {
    pub fn new() -> Handler {
        Handler
    }
}

pub unsafe fn init() {}

pub unsafe fn cleanup() {}
