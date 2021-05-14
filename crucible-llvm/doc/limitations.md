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
