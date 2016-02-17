# Symbolic Execution

Analysis of Java and LLVM within SAWScript builds heavily on *symbolic
execution*, so some background on how this process works can help with
understanding the behavior of the available built-in functions.

At the most abstract level, symbolic execution works like normal program
execution except that the values of all variables within the program
can be arbitary *expressions*, rather than concrete values, potentially
containing mathematical variables. As a concrete example, consider the
following C program, which returns the maximum of two values:

~~~~ {.c}
int max(int x, int y) {
    if (y > x) {
        return y;
    } else {
        return x;
    }
}
~~~~

If you call this function with two concrete inputs, like this:

~~~~ {.c}
int r = max(5, 4);
~~~~

then it will assign the value `5` to `r`. However, we can consider what
it will do for *arbitrary* inputs, as well. In the following example:

~~~~ {.c}
int r = max(a, b);
~~~~

we could describe the general value of `r` as follows:

~~~~
ite (b > a) b a
~~~~

where `ite` is the "if-then-else" mathematical function that, based on
the value of its first argument returns either the second or third.

A symbolic execution system, then, is very similar to an interpreter
with a different notion of what constitutes a value. Therefore, the
execution process follows a similar process to that of a normal
interpreter, and the process of generating a model for a piece of code
is similar to building a test harness for that same code.

More specifically, the setup process typically takes the following form:

* Initialize or allocate any resources needed by the code. For Java and
  LLVM code, this typically means allocating memory and setting the
  initial values of variables.

* Execute the code.

* Check the desired properties of the system state after the code
  completes.

Accordingly, three pieces of information are particularly relevant to
the symbolic execution process, and therefore needed as input to the
symbolic execution system:

* The initial state of the system.

* The code to execute.

* The final state of the system, and which parts of it are relevant to
  the properties being tested.

In the following sections, we describe how the Java and LLVM analysis
primitives work in the context of these key concepts. We start with the
simplest situation, in which the structure of the initial and final
states can be directly inferred, and move on to more complex cases that
require more information from the user.

# Symbolic Termination

TODO

# Loading Code

TODO: describe code loading process

# Direct Extraction

In the case of the `max` function described earlier, the relevant inputs
and outputs are directly apparent. The function takes two integer
arguments, always uses both of them, and returns a single integer value,
making no other changes to the program state.

In cases like this, a direct translation is possible, given only an
identification of which code to execute. Two functions exist to handle
such simple code:

    java_extract : JavaClass -> String -> JavaSetup () -> TopLevel Term 

    llvm_extract : LLVMModule -> String -> LLVMSetup () -> TopLevel Term

The structure of these two functions is essentially identical. The first
argument describes where to look for code (in either a Java class or an
LLVM module, loaded as described in the previous section). The second
argument is the name of the function or method to extract.

The third argument provides the ability to configure other aspects of
the symbolic execution process. At the moment, two options are possible.
If you pass in `java_pure` or `llvm_pure`, respectively, the default
extraction process is simply to set both arguments to fresh symbolic
variables, and return the symbolic value returned by the function or
method under analysis. The `java_sat_branches b` (or `llvm_sat_branches
b`) function explicitly turns on branch satisfiability checking, which
can help with symbolic termination issues, as described earlier. In the
future, other configuration may be possible.

When the `*_extract` functions complete, they return a `Term`
corresponding to the value returned by the function or method.

These functions work only for code that takes some fixed number of
integral parameters, returns an integral result, and does not access any
dynamically-allocated memory.

TODO: talk about proof

# Creating Symbolic Variables

TODO

# Monolithic Symbolic Execution

TODO: examples

In many cases, the values read by a function, and the effects produced
by it, are more complex than supported by the direct extraction process
just described. In that case, it's necessary to provide more
information. In particular, following the structure described earlier,
we need:

* For every pointer or object reference, how much storage space it
  refers to.
* A list of (potentially symbolic) values for some elements of the
  initial program state.
* A list of elements of the final program state to treat as outputs.

This capability is provided by the following built-in functions:

    java_symexec : JavaClass ->
                   String ->
                   [(String, Term)] ->
                   [String] ->
                   Bool ->
                   TopLevel Term

    llvm_symexec : LLVMModule ->
                   String ->
                   [(String, Int)] ->
                   [(String, Term, Int)] ->
                   [(String, Int)] ->
                   Bool ->
                   TopLevel Term

For both functions, the first two arguments are the same as for the
direct extraction functions from the previous section, identifying what
code to execute. The final argument for both indicates whether or not to
do branch satisfiability checking.

The remaining arguments are slightly different for the two functions,
due to the differences between JVM and LLVM programs.

For `java_symexec`, the third argument, of type `[(String, Term)]`,
provides information to configure the initial state of the program. Each
`String` is an expression describing a component of the state, such as
the name of a parameter, or a field of an object. Each `Term` provides
the initial value of that component.

The syntax of these expressions is as follows:

  * Arguments to the method being analyzed can be referred to by name
    (if the `.class` file contains debugging information, as it will be
    if compiled with `javac -g`). . The expression referring to the
    value of the argument `x` in the `max` example is simply `x`. For
    Java methods that do not have debugging information, arguments can
    be named positionally with `args[0]`, `args[1]` and so on. The name
    `this` refers to the same implicit parameter as the keyword in Java.

  * The expression form `pkg.C.f` refers to the static field `f` of
    class `C` in package `pkg`.

  * The expression `return` refers to the return value of the method
    under analysis.

  * For an expression `e` of object type, `e.f` refers to the instance
    field `f` of the object described by `e`.
  
  * The value of an expression of array type is the entire contents of
    the array. At the moment, there is no way to refer to individual
    elements of an array.

The fourth argument of `java_symexec` is a list of expressions
describing the elements of the state to return as outputs. The returned
`Term` will be of tuple type if this list contains more than one
element, or simply the value of the one state element if the list
contains only one.

The `llvm_symexec` command uses an expression syntax similar to that for
`java_symexec`, but not identical. The syntax is as follows:

  * Arguments to the function being analyzed can be referred to by name
    (if the name is reflected in the LLVM code, as it generally is with
    Clang). The expression referring to the value of the argument `x` in
    the `max` example is simply `x`. For LLVM functions that do not have
    named arguments (such as those generated by the Rust compiler, for
    instance), arguments can be named positionally with `args[0]`,
    `args[1]` and so on.

  * Global variables can be referred to directly by name.

  * The expression `return` refers to the return value of the function
    under analysis.

  * For any valid expression `e` referring to something with pointer
    type, the expression `*e` refers to the value pointed to. There are
    some differences between this and the equivalent expression in C,
    however. If, for instance, `e` has type `int *`, then `*e` will have
    type `int`. If `e` referred to a pointer to an array, the C
    expression `*e` would refer to the first element of that array. In
    SAWScript, it refers to the entire contents of the array, and there
    is no way to refer to individual elements of an array.

  * For any valid expression `e` referring to a pointer to a `struct`,
    the expression `e->n`, for some natural number `n`, refers to the
    `n`th field of that `struct`. Unlike the `struct` type in C, the
    LLVM `struct` type does not have named fields, so fields are
    described positionally. At the moment, there is no way to refer to
    fields of `struct`s that are referred to without a pointer, which
    also means that it is impossible to refer to fields of nested
    `struct`s.

In addition to the different expression language, the arguments are
similar but not identical. The third argument, of type
`[(String, Int)]`, indicates for each pointer how many elements it
points to. Before execution, SAW will allocate the given number of
elements of the static type of the given expression. The strings given
here should be expressions identifying *pointers* rather than the values
of those pointers.

The fourth argument, of type `[(String, Term, Int)]` indicates the
initial values to write to the program state before execution. TODO: say
more, including that the `String`s should be *value* expressions.

Finally, the fifth argument, of type `[(String, Int)]` indicates the
elements to read from the final state. For each entry, the `String`
should be an r-value, and the `Int` parameter indicates how many
elements to read. The number of elements does not need to be the same as
the number of elements allocated or written in the initial state.
However, reading past the end of an object or reading a location that
has not been initialized will lead to an error.

## Limitations

Although the `symexec` functions are more flexible than the `extract`
functions, they also have some limitations and assumptions.

* When allocating memory for objects or arrays, each allocation is done
  independently. Therefore, there is currently no way to create data
  structures that share sub-structures. No aliasing is possible.
  Therefore, it is important to take into account that any proofs
  performed on the results of symbolic execution will not necessarily
  reflect the behavior of the code being analyzed if it is called in a
  context where its inputs involve aliasing or overlapping memory
  regions.

* The sizes and pointer relationships between objects in the heap must
  be specified before doing symbolic execution. Therefore, the results
  may not reflect the behavior of the code when called with, for
  example, arrays of different sizes.

* In Java, any variables of class type are initialized to refer to an
  object of that specific, statically-declared type, while in general
  they may refer to objects of subtypes of that type. Therefore, the
  code under analysis may behave differently when given parameters of
  more specific types.

* TODO: anything else?

# Specification-Based Verification

The built-in functions described so far work by extracting models of
code which can then be used for a variety of purposes, including proofs
about the properties of the code.

When the goal is to prove equivalence between some Java or LLVM code and
a specification, however, sometimes a more declarative approach is
convenient. The following two functions allow for combined model
extraction and verification.

    java_verify : JavaClass ->
                  String ->
                  [JavaMethodSpec] ->
                  JavaSetup () ->
                  TopLevel JavaMethodSpec

    llvm_verify : LLVMModule ->
                  String ->
                  [LLVMMethodSpec] ->
                  LLVMSetup () ->
                  TopLevel LLVMMethodSpec

Like all of the functions for Java and LLVM analysis, the first two
parameters indicate what code to analyze. The third parameter is used
for compositional verification, as described in the next section. For
now, assume that it is always the empty list. The final parameter
describes the specification of the code to be analyzed. Specifications
are slightly different between Java and LLVM, but make use of largely
the same set of concepts.

* Several commands are available to configure the contents of the
  initial state, before symbolic execution.

* Several commands configure the behavior of symbolic execution overall.

* Several commands are available to describe what to check of the final
  state, after symbolic execution.

* One final command describes how to prove that the code under analysis
  matches the specification.

## Configuring the Initial State

TODO

    java_assert
    java_var
    java_class_var
    java_may_alias

    llvm_assert
    llvm_assert_eq
    llvm_var
    llvm_ptr

    java_byte
    java_char
    java_short
    java_int
    java_long
    java_float
    java_double
    java_class
    
    llvm_int
    llvm_array
    llvm_struct
    llvm_float
    llvm_double

## Controlling Symbolic Execution

TODO

    java_no_simulate
    java_sat_branches
    java_allow_alloc

    llvm_no_simulate
    llvm_sat_branches

## Checking the Final State

TODO

    mention "return" variable

    java_ensure_eq
    java_return

    llvm_ensure_eq
    llvm_return

## Running Proofs

TODO

    java_verify_tactic

    llvm_verify_tactic

# Compositional Verification

The primary advantage of the specification-based approach to
verification is that it allows for compositional reasoning.

TODO
