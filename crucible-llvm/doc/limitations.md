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


Floating-point accuracy
=======================

The implementations of some floating-point operations are imprecise with
respect to NaN values. For example, `crucible-llvm`'s implementation of the
`copysign` function will always return a positive, "quiet" NaN value if its
first argument is a NaN, regardless of the sign of the second argument.


`freeze` instruction limitations
================================
`crucible-llvm` handles LLVM's
[`freeze` instruction](https://releases.llvm.org/12.0.0/docs/LangRef.html#freeze-instruction)
somewhat inaccurately. LLVM's intended semantics for `freeze` state that
if the argument is an `undef` or `poison` value, then `freeze` should return
an arbitrary value; otherwise, it should return the argument unchanged. In
`crucible-llvm`, however, a `freeze` instruction _always_ returns the argument
unchanged. The issue is that `crucibe-llvm` currently does not have the ability
to reliably determine whether a given value is `undef` or `poison`.

One can often get close to the intended LLVM semantics for `freeze` by enabling
the `lax-loads-and-stores` option, which makes `load`s from uninitialized
memory yield arbitrary values. Since LLVM often passes loaded values
from uninitialized memory to `freeze` to ensure that the result is not
`undef`, this will ensure that a sizable number of use cases for
`freeze` will be handled as expected.
