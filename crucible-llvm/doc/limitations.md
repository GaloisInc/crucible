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
the specification. Most notably:

* We do not correctly display precision for floating-point values.
* We do not implement the `%a` conversion code for binary formatted
  floating-point values.
* We assume that all characters in C strings are exactly 1 byte in size, which
  means that format strings using `%ls` will likely not work as expected.
* We will simply print a collection of `?` characters for symbolic
  values.

Thus the exact printed output, number of characters printed, etc,
may not exactly match that of a conforming implementation.


Floating-point limitations
==========================

`crucible-llvm`'s handling of floating-point operations are imprecise in
several aspects:

## Floating-point accuracy

The implementations of some floating-point operations are imprecise with
respect to NaN values. For example, `crucible-llvm`'s implementation of the
`copysign` function will always return a positive, "quiet" NaN value if its
first argument is a NaN, regardless of the sign of the second argument.

## Floating-point exceptions

`crucible-llvm` currently makes no effort to model floating-point exceptions
that arise from invoking certain floating-point operations. For instance,
invoking the `sqrt` function on a negative value will never result in an
invalid floating-point exception being raised.

## Floating-point rounding modes

`crucible-llvm` currently makes no effort to track different floating-point
rounding modes, and the `fegetround`/`fesetround` functions are not yet
modeled. Whenever the result of a floating-point operation cannot be exactly
represented in the significand, `crucible-llvm` will default to rounding the
result toward the nearest even number.

## Evaluation of floating-point functions

`crucible-llvm` treats the following floating-point operations over `double`s
as uninterpreted functions:

* `sin`
* `cos`
* `tan`
* `asin`
* `atan`
* `acos`
* `sinh`
* `cosh`
* `tanh`
* `asinh`
* `acosh`
* `atanh`
* `hypot`
* `atan2`
* `exp`
* `log`
* `expm1`
* `log1p`
* `log2`
* `exp10`
* `log10`

Similar treatment is given to the `float` counterparts of these functions (e.g.,
`sinf`). Because they are treated as uninterpreted, `crucible-llvm`'s ability
to reason about expressions involving these functions is limited to basic,
syntactic equivalence checking.

`freeze` instruction limitations
================================
`crucible-llvm` handles LLVM's
[`freeze` instruction](https://releases.llvm.org/12.0.0/docs/LangRef.html#freeze-instruction)
somewhat inaccurately. LLVM's intended semantics for `freeze` state that
if the argument is an `undef` or `poison` value, then `freeze` should return
an arbitrary value; otherwise, it should return the argument unchanged. In
`crucible-llvm`, however, a `freeze` instruction _always_ returns the argument
unchanged. The issue is that `crucible-llvm` currently does not have the ability
to reliably determine whether a given value is `undef` or `poison`.

One can often get close to the intended LLVM semantics for `freeze` by enabling
the `lax-loads-and-stores` option, which makes `load`s from uninitialized
memory yield arbitrary values. Since LLVM often passes loaded values
from uninitialized memory to `freeze` to ensure that the result is not
`undef`, this will ensure that a sizable number of use cases for
`freeze` will be handled as expected.

LLVM poison limitations
=======================
`crucible-llvm` has limited support for tracking
[poison values](https://releases.llvm.org/13.0.0/docs/LangRef.html#poisonvalues).
Certain LLVM instructions and intrinsics can return poison values under
certain circumstances, and `crucible-llvm` makes an effort to generate failing
assertions whenever such poison values are returned. For instance, LLVM's
`add` instruction can return poison if the result overflows, which
`crucible-llvm` is able to detect and simulate by throwing an appropriate
assertion failure.

There are other ways to create and propagate poison that `crucible-llvm` cannot
track as well, however. In particular, LLVM features `poison` constant values
that can take on values of any type, which means that they can be propagated to
any part of a program. `crucible-llvm` has extremely limited support for
representing `poison` constant values, but only in circumstances where `poison`
values are not simulated directly. As an example of what "simulated directly"
means, consider the following example:

```llvm
define i32 @main() {
  %v = insertelement <2 x i32> <i32 poison, i32 1>, i32 0, i64 0
  %r = extractelement <2 x i32> %v, i32 0
  ret i32 %r
}
```

Note that `poison` appears as the first element of the vector passed to the
`insertelement` instruction. `crucible-llvm` is able to simulate this program,
however. This is because the `insertelement` instruction will replace the
`poison` element with `0`, which means that by the time this instruction makes
it to Crucible's simulator, the value that gets simulated will be a vector
containing `0` and `1`.

This is not to say that intermediate `poison` values will always be translated
away, however. For instance, `crucible-llvm` does not support the following
variation of the program above:

```llvm
define i32 @main() {
  %v1 = insertelement <2 x i32> <i32 42, i32 1>, i32 poison, i64 0
  %v2 = insertelement <2 x i32> %v1, i32 0, i64 0
  %r = extractelement <2 x i32> %v2, i32 0
  ret i32 %r
}
```

This is because the `%v1` register contains a `poison` value in the first
element of its vector, and when attempting to translate `%v1` to a simulator
value, `crucible-llvm` gives up when it encounters `poison`. As a general rule,
`poison` values are permitted provided that they do not end up stored in
registers or in memory.
