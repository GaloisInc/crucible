//! This is an internal module used by the ifmt! runtime. These structures are
//! emitted to static arrays to precompile format strings ahead of time.
//!
//! These definitions are similar to their `ct` equivalents, but differ in that
//! these can be statically allocated and are slightly optimized for the runtime
#![allow(missing_debug_implementations)]

#[derive(Copy, Clone)]
pub struct Argument {
    pub position: Position,
    pub format: FormatSpec,
}

#[derive(Copy, Clone)]
pub struct FormatSpec {
    pub fill: char,
    pub align: Alignment,
    pub flags: u32,
    pub precision: Count,
    pub width: Count,
}

#[derive(Copy, Clone, PartialEq, Eq)]
pub enum Alignment {
    Left,
    Right,
    Center,
    Unknown,
}

#[derive(Copy, Clone)]
pub enum Count {
    Is(usize),
    Param(usize),
    NextParam,
    Implied,
}

#[derive(Copy, Clone)]
pub enum Position {
    Next,
    At(usize),
}
