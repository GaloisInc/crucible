# Bitvector Abstract Domain Formalization

The module `What4.Utils.BVDomain` implements an abstract domain for
sized bitvectors, using an interval-based representation. Many of the
algorithms in this module are subtle and not obviously correct.

To increase confidence in the correctness of that code, the file
`bvdomain.cry` in this directory contains a formalization of those
algorithms in Cryptol (<https://cryptol.net>).

Use the following command to prove all of the correctness properties
in the Cryptol specification using the z3 prover:

    cryptol bvdomain.cry -c :prove

NOTE: This verification only asserts the correctness of the Cryptol
specification, not of the actual Haskell implementation; the
correspondence between the Haskell and Cryptol versions must be
checked by manual inspection. Keep in mind that the Haskell version
uses the unbounded `Integer` type throughout, and uses bitwise masking
to reduce modulo 2^n; on the other hand, the Cryptol code uses
fixed-width bitvector types where this masking is implicit. Otherwise
the structure of the code is very similar.
