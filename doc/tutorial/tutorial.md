% **SawScript**
% Galois, Inc. | 421 SW 6th Avenue, Suite 300 | Portland, OR 97204

\newpage

Introduction
============

Example: Find First Set
=======================

Algorithm
---------

TODO: describe problem

Reference Implementation
-------------------------

``` {.c}
$include 1-9 code/ffs.c
```

TODO: show reference version

Optimized Implementation
------------------------

``` {.c}
$include 11-18 code/ffs.c
```

TODO: show implementation version

Generating LLVM Code
--------------------

TODO: show bitcode generation

Equivalence Proof
-----------------

TODO: show proof of equivalence using built-in ABC

```
$include all code/ffs.saw
```

Cross-Language Proofs
---------------------

TODO: show proof between C and Java versions

Example: SHA-384
================

Algorithm Structure
-------------------

Downloading the Bouncy Castle Implementation
--------------------------------------------

Overview of Cryptol Implementation
----------------------------------

```
$include 12-28 code/SHA384.cry
```

Proving Functions Equivalent
----------------------------

Using SMT-Lib Solvers
=====================

The examples presented so far have used the internal proof system
provided by SAWScript, based primarily on a version of the ABC tool
from UC Berkeley linked into the `saw` executable. However, other
proof tools can be used, as well. The current version of SAWScript
includes support for exporting models representing theorems as goals
in the SMT-Lib language. These goals can then be solved using an
external SMT solver such as Yices or CVC4.

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

  * Support for automatic invocation of SMT solvers and interpretation
    of their output.
  * Support for generation of (Q)DIMACS CNF and QBF files, for use
    with SAT and QBF solvers.
  * Support for automatic invocation of SAT and QBF solvers, and
    interpretation of their output.

Improved Support for Manipulating Formal Models
-----------------------------------------------

  * Specifying and applying rewrite rules to simplify formal models.
  * Applying formal models directly to concrete arguments.
  * Applying formal models automatically to a large collection of
    randomly-generated concrete arguments.

Summary
=======
