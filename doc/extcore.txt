Introduction
============

Consider the following example SAWScript program:

```
main = do {
  let excluded_middle x = x || not x;
  print_term excluded_middle;
  write_core "excluded_middle.extcore" excluded_middle;
};
```

The `print_term` command pretty prints the representation of
`excluded_middle` as a term in the core language.

```
\(x::Prelude.Bool) -> Prelude.or x (Prelude.not x)
```

The `write_core` command outputs a file in a more easily
computer-readable `extcore` format. (The format can then be read in by
the `read_core` command.)

```
SAWCoreTerm 8
1 Data Prelude.Bool
2 Global Prelude.or
3 Var 0
4 App 2 3
5 Global Prelude.not
6 App 5 3
7 App 4 6
8 Lam x 1 7
```

An `extcore` file encodes a single term of the core language by
assigning a numeric index to each of its unique subterms.

Each line in an `extcore` file consists of a sequence of tokens
separated by whitespace. The tokens may be names (alphanumeric
identifiers, possibly including dot-separated qualifiers), numeric
indexes, or literals. The first line is a header containing the magic
string `SAWCoreTerm` followed by the index of the final term (i.e.,
the output term).

Each subsequent line defines a new term, following a standard format:
First is the new index to be defined, then a keyword indicating what
kind of term, and finally a sequence of tokens (the number and type of
which determined by the keyword). Each line can refer to any
previously defined index.

In the following table, angle brackets enclose descriptions of each
argument. Parentheses and asterisks are used to describe patterns of
valid arguments, and will not show up in files.

Form                                                     Description
-----------------------------------------------------    -----------
`ExtCns <input number> <name> <index(type)>`             External input
`Lam <name> <index(type)> <index(body)>`                 Function abstraction
`Pi <name> <index(argument type)> <index(result type)>`  Function type
`Var <integer literal> <index(type)>`                    Bound variable (de Bruijn indexed)
`Global <qualified name>`                                Toplevel constant
`App <index(function)> <index(argument)>`                Function application
`Tuple <index(component)>*`                              Tuple value
`TupleT <index(type)>*`                                  Tuple type
`TupleSel <index> <field number>`                        Tuple component selector (`x.1`)
`Record (<field name> <index(component)>)*`              Record value
`RecordT (<field name> <index(type)>)*`                  Record type
`RecordSel <index> <field name>`                         Record component selector (`x.foo`)
`Ctor <qualified name> <index(argument)>*`               Data constructor value
`Data <qualified name> <index(type)>*`                   Datatype
`Sort <integer literal>`                                 Sort
`Nat <integer literal>`                                  Non-negative integer literal
`Array <index(type)> <index(element)>*`                  Array value (e.g. `[1, 2, 3]`)
`Float <float literal>`                                  Literal of type `Float`
`Double <double literal>`                                Literal of type `Double`
`String <string literal>`                                Literal of type `String`

The following sections describe each of these keywords in more detail.

Inputs and Scalar Constants
===========================

The simplest terms in `extcore` refer to external inputs and constant
values. Two types of external inputs exist.

The `ExtCns` keyword indicates an input identified by index, with a
declared type, and a name that exists primarily as a comment. Inputs
of this type are most appropriate when thinking of the term as a
representation of a circuit.

The `Global` keyword indicates a global term identified by name. This
keyword is primarily used to refer to built-in operators, such as
prelude functions that operate on bit vectors.

Constants can be written with one of the keywords `Nat`, `Float`,
`Double`, or `String`, followed by the value of the constant. Bit
vector constants can be created by applying the function described in
the "Bit Vectors" section that converts a natural number to a bit
vector. Later sections describe how to write aggregated or structured
constants.

Applications
============

Computations in SAWCore are accomplished by applying operators (or any
term of function type) to operands. Application is structured in
"curried" form: each application node applies a node of function type
to one argument. Functions that take multiple arguments require
multiple application nodes. For example, to add two 8-bit bit vectors,
we can use the following code:

```
1 Global Prelude.bitvector
2 Nat 8
3 App 1 2
4 ExtCns 0 "x" 3
5 ExtCns 1 "y" 3
6 Global Prelude.bvAdd
7 App 6 2
8 App 7 4
9 App 8 5
```

This snippet applies the builtin `bitvector` type to the natural
number 8, to form the type of the input variables. These inputs are
then declared on lines 4 and 5. Line 7 then applies the builtin
`bvAdd` to the natural number 8 (to tell it the size of the following
bit vectors). Finally, lines 8 and 9 continue the application to
include the two input variables.

Booleans and Bit Vectors
========================

The previous section gave an example of a bit vector operation. The
SAWCore prelude contains a number of built-in operations on both bit
vectors and booleans.

Th `bvNat` function constructs a constant bit vector, of a given size,
from the given natural number. Conversely, the `bvToNat` function
takes a bit vector length, a vector of this length, and returns the
corresponding natural number.

The usual bit vector operators work on one or more bit vectors of a
single vector size. These functions take a natural number as their
first argument, indicating the size of the following bit vectors.

There are a few exceptions to this general pattern. The unsigned bit
vector shifting operations take a natural number as their second
operand. All signed bit vector operations take a natural number one
smaller than the size of their remaining arguments (to ensure that
their arguments have non-zero size). The `bvAppend` operator takes two
natural numbers, corresponding to the lengths of its two bit vector
arguments, and returns a bit vector with length correponding to the
sum of the lengths of its arguments.

The complete collection of bit vector operations appears in the
Reference section at the end of this document.

Arrays, Tuples and Records
==========================

SAWCore allows aggregation of arbitrary data types into composite
types: arrays, tuples, and records. Arrays are collections, of known
size, containing multiple values of the same type. Tuples contain a
list of values that match, in order, a given list of types. Records
are like tuples with named rather than numbered fields.

For each of these composite forms, SAWCore includes constructs for
building both types and values.

To construct an array type, apply the builtin `prelude.Vec` to the
desired size followed by the type of its elements. To construct an
array value, use the keyword `Array` followed by the node index of its
type, and then all of the node indices of its elements. Bit vectors in
SAWCore are actually just arrays of boolean values.

To construct a tuple type, use the `TupleT` keyword followed by the
indices of the individual element types. To construct a tuple value,
use the `Tuple` keyword followed by the indices of the individual
element values. Finally, to select an element from a tuple value, use
the `TupleSel` keyword followed by the index of the tuple value and
then the element number to extract.

Record types and values are like tuple types and values, except that
each type or value index is preceded by a field name. Record field
selection is identical to tuple element selection except that it uses
a field name instead of an element index.

Function Abstractions
=====================

SAWCore allows the creation of function abstractions. The construct
`Lam <type> <body>` causes a function argument value of the given type
to be bound within the term specified by the second argument.
Functions with multiple arguments are constructed with multiple nested
`Lam` nodes. Within the term, an argument can be accessed by the
construct `Var <n> <type>` where an index of `0` corresponds to the
variable bound by the most recent enclosing `Lam`, an index of `1`
corresponds to the variable bound by a `Lam` one level removed, and so
on. Function abstractions can allow code to be abstracted over
different arguments, and applied multiple times in multiple contexts.
They can also be used as an alternative to the `ExtCns` inputs
described previously.

As an example, the code presented earlier in the Application section,
to add two 8-bit bit vector arguments, could be restructured to use
`Lam` and `Var` as follows:

```
1 Global Prelude.bitvector
2 Nat 8
3 App 1 2
4 Global Prelude.bvAdd
5 App 4 2
6 Var 0 3
7 Var 1 3
8 App 5 6
9 App 8 7
10 Lam x 3 9
11 Lam x 3 10
```

Custom Data Types
=================

Several built-in data types, such as records and tuples, have
dedicated syntax within the language. Other data types, however,
including vectors and booleans, are defined as a set of type
constructors and data constructors.

Type constructors, including `Vec` and `Bool`, take zero or more
arguments inline (i.e., they are not applied with the `App` form), and
create a node corresponding to a data type. The `Bool` type
constructor takes no arguments, while the `Vec` constructor takes two,
a natural number representing its size followed by the type index of
its elements.

To create a value of a type specified by one of these type
constructors, apply one of the zero or more data constructors
associated with the type. Each data constructor may take zero or more
arguments.

Boolean values (corresponding to type constructor `Bool`) can be
constructed with the two data constructors `True` and `False`, both of
which take zero arguments.

Values of vector type can be constructed in two ways. The built-in form
`Array` takes a type index (corresponding to the element type) as its
first argument, followed by a sequence of element expression indices.

Alternatively, vector values can be constructed piece-by-piece using
the two data constructors:

  * `EmptyVec` which takes a type as an argument and produces a vector
    with zero elements of that type, and

  * `ConsVec` which takes a type, a value, a size, and an existing
    vector of that given size, and produces a new vector of size one
    larger, with the given element value at the beginning.

Other type and data constructors exist in the SAWCore prelude, but
they rarely occur in terms exported for analysis by third-party tools.

Reference
=========

This section summarizes the built-in types, boolean functions, and bit
vector functions defined in the SAWCore prelude. These types and
functions will apppear in `extcore` files in the form
`Prelude.<name>`, but are listed below in the form `<name>`, without
the `Prelude` prefix, for brevity and readability.

Prelude types:

Name             Kind               Comments
----             ----               --------
`Bool`           `Type`
`Nat`            `Type`
`bitvector`      `Nat -> Type`      Abbreviation for `Vec n Bool`
`Vec`            `Nat -> Type -> Type`
`String`         `Type`

Prelude boolean functions:

Name             Type
----             ----
`and`            `Bool -> Bool -> Bool`
`or`             `Bool -> Bool -> Bool`
`xor`            `Bool -> Bool -> Bool`
`boolEq`         `Bool -> Bool -> Bool`
`not`            `Bool -> Bool`
`ite`            `(a:Type) -> Bool -> a -> a -> a`

Prelude bit vector functions:

Name             Type
----             ----
`msb`            `(n:Nat) -> bitvector (n + 1) -> Bool`
`bvNat`          `(n:Nat) -> Nat -> bitvector n`
`bvToNat`        `(n:Nat) -> bitvector n -> Nat`
`bvAdd`          `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvSub`          `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvMul`          `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvUDiv`         `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvURem`         `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvSDiv`         `(n:Nat) -> bitvector (n + 1) -> bitvector (n + 1) -> bitvector (n + 1)`
`bvSRem`         `(n:Nat) -> bitvector (n + 1) -> bitvector (n + 1) -> bitvector (n + 1)`
`bvAnd`          `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvOr`           `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvXor`          `(n:Nat) -> bitvector n -> bitvector n -> bitvector n`
`bvNot`          `(n:Nat) -> bitvector n -> bitvector n`
`bvShl`          `(n:Nat) -> bitvector n -> Nat -> bitvector n`
`bvShr`          `(n:Nat) -> bitvector n -> Nat -> bitvector n`
`bvSShr`         `(n:Nat) -> bitvector (n + 1) -> bitvector n -> bitvector (n + 1)`
