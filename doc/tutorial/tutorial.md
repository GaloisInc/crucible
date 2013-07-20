% **SawScript**
% Galois, Inc. | 421 SW 6th Avenue, Suite 300 | Portland, OR 97204

\newpage

Introduction
============

The SAWScript language is a special-purpose programming language
developed by Galois to help orchestrate and track the results of the
large collection of proof tools necessary for analysis and
verification of complex software artifacts.

The language adopts the functional paradigm, and largely follows the
structure of many other functional languages, with some special
features specifically targeted at the coordination of verification
tasks.

This tutorial introduces the details of the language by walking
through several examples, and showing how simple verification tasks
can be described.

Example: Find First Set
=======================

As a first example, we consider a simple function that identifies the
first ``1`` bit in a word. The function takes an integer as input,
treated as a vector of bits, and returns another integer which
indicates the index of the first bit set. This function exists in a
number of standard C libraries, and can be implemented in several
ways.

Reference Implementation
-------------------------

One simple implementation take the form of a loop in which the index
starts out at zero, and we keep track of a mask initialized to have
the least signficant bit set. On each iteration, we increment the
index, and shift the mask to the left. Then we can use a bitwise "and"
operation to test the bit at the index indicated by the index
variable. The following C code uses this approach.

``` {.c}
$include 1-9 code/ffs.c
```

This implementation is relatively straightforward, and a proficient C
programmer would probably have little difficulty believing its
correctness. However, the number of branches taken during execution
could be as many as 32, depending on the input value. It's possible to
implement the same algorithm with significantly fewer branches, and no
backward branches.

Optimized Implementation
------------------------

An alternative implementation, taken by the following program, treats
the bits of the input word in chunks, allowing sequences of zero bits
to be skipped over more quickly.

``` {.c}
$include 11-18 code/ffs.c
```

However, this code is much less obvious than the previous
implementation. If it is correct, we would like to use it, since it
has the potential to be faster. But how do we gain confidence that it
calculates the same results as the original program?

SAWScript allows us to state this problem concisely, and to quickly
and automatically prove the equivalence of these two functions for all
possible inputs.

Generating LLVM Code
--------------------

The SAWScript interpreter knows how to analyze LLVM code, but most
programs are originally written in a higher-level language such as C,
as in our example. Therefore, the C code must be translated to LLVM,
using something like the following command:

```
$cmd clang -c -emit-llvm -o code/ffs.bc code/ffs.c
```

Equivalence Proof
-----------------

We now show how to use SAWScript to prove the equivalence of the
reference and implementation versions of the FFS algorithm.

A SAWScript program is typically structured as a set of commands
within a `main` function, potentially along with other functions
defined to abstract over commonly-used combinations of commands.

The following script is sufficient to automatically prove the
equivalence of the `ffs_ref` and `ffs_imp` functions.

```
$include all code/ffs_llvm.saw
```

In this script, the `print` commands simply display text for the user.
The `llvm_extract` command instructs the SAWScript interpreter to
perform symbolic simulation of the given C function (e.g., `ffs_ref`)
from a given bitcode file (e.g., `ffs.bc`), and return a term
representing the semantics of the function. The final argument,
`llvm_pure` indicates that the function to analyze is a "pure"
function, which computes a scalar return value entirely as a function
of its scalar parameters.

The `let` statement then constructs a new term corresponding to the
assertion of equality between two existing terms. The `prove` command
can verify the validity of such an assertion. The `abc` parameter
indicates what theorem prover to use.

Cross-Language Proofs
---------------------

We can implement the FFS algorithm in Java with code almost identical
to the C version.

The reference version uses a loop, like the C version:

``` {.java}
$include 2-10 code/FFS.java
```

And the efficient implementation uses a fixed sequence of masking and
shifting operations:

``` {.java}
$include 12-19 code/FFS.java
```

Although in this case we can look at the C and Java code and see that
they perform almost identical operations, the low-level operators
available in C and Java do differ somewhat. Therefore, it would be
nice to be able to gain confidence that they do, indeed, perform the
same operation.

We can do this with a process very similar to that used to compare the
reference and implementation versions of the algorithm in a single
language.

First, we compile the Java code to a JVM class file.

```
$cmd javac -g code/FFS.java
```

Now we can do the proof both within and across languages:

```
$include all code/ffs_compare.saw
```

Using SMT-Lib Solvers
=====================

The examples presented so far have used the internal proof system
provided by SAWScript, based primarily on a version of the ABC tool
from UC Berkeley linked into the `saw` executable. However, other
proof tools can be used, as well. The current version of SAWScript
includes support for exporting models representing theorems as goals
in the SMT-Lib language. These goals can then be solved using an
external SMT solver such as Yices or CVC4.

Consider the following C file:

```
$include all code/double.c
```

In this trivial example, an integer can be doubled either using
multiplication or shifting. The following SAWScript program verifies
that the two are equivalent using both ABC, and by exporting an
SMT-Lib theorem to be checked by an external solver.

```
$include all code/double.saw
```

The new primitives introduced here are `not`, which constructs the
logical negation of a term, and `write_smtlib1`, which writes a term
as a proof obligation in SMT-Lib version 1 format. Because SMT solvers
are satisfiability solvers, negating the input term allows us to
interpret a result of "unsatisfiable" from the solver as an indication
of the validity of the term.

At the moment, SMT-Lib version 1 is best supported, though version 2
is implemented for a smaller number of primitives. Writing SMT-Lib
files tends to work well only with terms constructed from LLVM or SBV
input files. The JVM simulator and AIG reading code construct terms
including primitives that the SMT-Lib exporter doesn't yet support.

Future Enhancements
===================

Improved Symbolic Simulation Control
------------------------------------

  * More sophisticated control over the symbolic simulation process,
    allowing a wider range of functions from imperative languages to
    be translated into formal models.
  * Support for compositional verification.

Improved Integration with External Proof Tools
----------------------------------------------

  * More complete SMT-Lib export support.
  * Support for automatic invocation of SMT solvers and interpretation
    of their output.
  * Support for generation of (Q)DIMACS CNF and QBF files, for use
    with SAT and QBF solvers.
  * Support for automatic invocation of SAT and QBF solvers, and
    interpretation of their output.

Improved Support for Manipulating Formal Models
-----------------------------------------------

  * Specifying and applying rewrite rules to simplify formal models.
  * Applying formal models directly to concrete arguments. (Done)
  * Applying formal models automatically to a large collection of
    randomly-generated concrete arguments.
