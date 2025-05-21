# Undefined behavior

This document describes which forms of undefined behaviors listed in the C11 standard Crucible-LLVM checks for.
Because the C standard does not offer a comprehensive numbering scheme, we adopt that of the back matter of the [SEI CERT C Coding Standard].

[SEI CERT C Coding Standard]: https://wiki.sei.cmu.edu/confluence/display/c/CC.+Undefined+Behavior

The following determinations are quite nuanced.
Please reach out to crux@galois.com if you have further questions about the properties checked by Crucible-LLVM.

Many undefined behaviors refer to the lexical and syntactic structure of the source C program.
Such behaviors are out of scope for Crucible-LLVM, which operates on LLVM bitcode.
This includes at least behaviors 2, 3, 4, 6, 7, 8, 14, 15, 26-31, 33, 34, 56-58, 60, and 90-96.

Additional behaviors refer to syntactic categories such as lvalues that do not have corollaries at the LLVM level.
This includes at least behaviors 12, 13, 18-21, 36, 46, 61, 62.

Further behaviors refer to types that are not available or semantically meaningful at the LLVM level, such as `void`. This includes at least behavior 22.

Some behaviors refer to the content of constant expressions.
These expressions are already simplified and processed by Clang as it lowers to LLVM, so these are also out of scope.
This includes at least behaviors 52-55.

The following table lists the remaining behaviors. It is far from complete, and we hope to expand it over time.

<!-- TODO(#85): The remaining rows, currently done up to 60 -->
<!-- TODO(#85): Investigate "?"s -->

| Number  | Description | Supported | Test case | Notes      |
| ------- | ----------- | --------- | --------- | ---------- |
| 5 | The execution of a program contains a data race (5.1.2.5). | No | | | Concurrency not supported |
| 9 | An object is referred to outside of its lifetime (6.2.4). | Yes | [009] | |
| 10 | The value of a pointer to an object whose lifetime has ended is used (6.2.4). | Yes | [009] | |
| 11 | The value of an object with automatic storage duration is used while the object has an indeterminate representation (6.2.4, 6.7.11, 6.8). | Yes | [011] | |
| 16 | Conversion to or from an integer type produces a value outside the range that can be represented (6.3.1.4). | ? | | |
| 17 | Demotion of one real floating type to another produces a value outside the range that can be represented (6.3.1.5). | ? | | |
| 23 | Conversion of a pointer to an integer type produces a value outside the range that can be represented (6.3.2.3). | Yes | | |
| 24 | Conversion between two pointer types produces a result that is incorrectly aligned (6.3.2.3). | ? | | |
| 25 | A pointer is used to call a function whose type is not compatible with the referenced type (6.3.2.3). | Yes | [025] | |
| 32 | The program attempts to modify a string literal (6.4.5). | Yes | | |
| 34 | A side effect on a scalar object is unsequenced relative to either a different side effect on the same scalar object or a value computation using the value of the same scalar object (6.5.1). | No | | Not applicable at the LLVM level |
| 35 | An exceptional condition occurs during the evaluation of an expression (6.5.1). | Yes | | |
| 37 | A function is defined with a type that is not compatible with the type (of the expression) pointed to by the expression that denotes the called function (6.5.3.3). | ? | | |
| 38 | A member of an atomic structure or union is accessed (6.5.3.4). | ? | | |
| 39 | The operand of the unary * operator has an invalid value (6.5.4.2). | Yes | [039] | |
| 40 | A pointer is converted to other than an integer or pointer type (6.5.5). | Yes | | |
| 41 | The value of the second operand of the / or % operator is zero (6.5.6). | Yes | | |
| 42 | If the quotient a/b is not representable, the behavior of both a/b and a%b (6.5.6). | Yes | | |
| 43 | Addition or subtraction of a pointer into, or just beyond, an array object and an integer type produces a result that does not point into, or just beyond, the same array object (6.5.7). | Yes | [043] | |
| 44 | Addition or subtraction of a pointer into, or just beyond, an array object and an integer type produces a result that points just beyond the array object and is used as the operand of a unary * operator that is evaluated (6.5.7). | Yes | [043] | |
| 45 | Pointers that do not point into, or just beyond, the same array object are subtracted (6.5.7). | Yes | [045] | |
| 46 | An array subscript is out of range, even if an object is apparently accessible with the given subscript (as in the lvalue expression `a[1][7]` given the declaration int `a[4][5]`) (6.5.7). | No | | Not applicable at the LLVM level |
| 47 | The result of subtracting two pointers is not representable in an object of type ptrdiff_t (6.5.7). | No | | Not applicable at the LLVM level |
| 48 | An expression is shifted by a negative number or by an amount greater than or equal to the width of the promoted expression (6.5.8). | Yes | | |
| 49 | An expression having signed promoted type is left-shifted and either the value of the expression is negative or the result of shifting would not be representable in the promoted type (6.5.8). | ? | | |
| 50 | Pointers that do not point to the same aggregate or union (nor just beyond the same array object) are compared using relational operators (6.5.9). | Yes | [050] | |
| 51 | An object is assigned to an inexactly overlapping object or to an exactly overlapping object with incompatible type (6.5.17.2). | ? | | |
| 59 | An attempt is made to access, or generate a pointer to just past, a flexible array member of a structure when the referenced object provides no elements for that array (6.7.3.2). | Yes | | |

[009]: ../../crucible-llvm-cli/test-data/ub/009.cbl
[011]: ../../crucible-llvm-cli/test-data/ub/011.cbl
[025]: ../../crucible-llvm-cli/test-data/ub/025.cbl
[039]: ../../crucible-llvm-cli/test-data/ub/039.cbl
[043]: ../../crucible-llvm-cli/test-data/ub/043.cbl
[045]: ../../crucible-llvm-cli/test-data/ub/045.cbl
[050]: ../../crucible-llvm-cli/test-data/ub/050.cbl
