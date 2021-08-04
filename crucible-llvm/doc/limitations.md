`crucible-llvm` limitations
---------------------------

Address space limitations
=========================

`crucible-llvm` currently assumes that all code uses the default address space
`0`. LLVM's data layout is permitted to declare multiple address spaces with
differing pointer sizes, however. For instance, LLVM 10 and later will
[reserve address spaces 270 through 272](https://reviews.llvm.org/D64931) in
X86 data layouts for the purpose of implementing mixed pointer sizes.
`crucible-llvm`, on the other hand, currently assumes that all pointers in a
given program are the same size, so it is unlikely that `crucible-llvm` would
work on code that uses differently sized address spaces. In practice,
`crucible-llvm` will only look at the part of the data layout which specifies
the default address space when determining what size pointers should be.


Printf accuracy
=====================

The `printf` implementation provided with `crucible-llvm` makes a
reasonable effort to implement the various conversion codes, but there
are some places where the formatting does not strictly conform to
the specification (most notably, regarding displayed precision for
floating-point values). We also do not implement the "%a" conversion
code for binary formatted floating-point values.
We also will simply print a collection of '?' characters for symbolic
values.

Thus the exact printed output, number of characters printed, etc,
may not exactly match that of a conforming implementation.
