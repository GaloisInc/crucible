% **SAWScript**
% Galois, Inc. | 421 SW 6th Avenue, Suite 300 | Portland, OR 97204

\newpage

Introduction
============

SAWScript is a special-purpose programming language developed by
Galois to help orchestrate and track the results of the large
collection of proof tools necessary for analysis and verification of
complex software artifacts.

The language adopts the functional paradigm, and largely follows the
structure of many other typed functional languages, with some special
features specifically targeted at the coordination of verification and
analysis tasks.

This tutorial introduces the details of the language by walking
through several examples, and showing how simple verification tasks
can be described.

Example: Find First Set
=======================

As a first example, we consider equivalence checking different implementations
of the POSIX `ffsl` function, which identifies the position of the first ``1``
bit in a word. The function takes an integer as input, treated as a vector of
bits, and returns another integer which indicates the index of the first bit
set. This function can be implemented in several ways with different
performance and code clarity tradeoffs, and we would like to show those
different implementations are equivalent.

Reference Implementation
-------------------------

One simple implementation takes the form of a loop with an index
initialized to zero, and a mask initialized to have the least
significant bit set. On each iteration, we increment the index, and
shift the mask to the left. Then we can use a bitwise "and" operation
to test the bit at the index indicated by the index variable. The
following C code (which is also in the `code/ffs.c` file accompanying
this tutorial) uses this approach.

``` {.c}
$include 9-17 code/ffs.c
```

This implementation is relatively straightforward, and a proficient C
programmer would probably have little difficulty believing its
correctness. However, the number of branches taken during execution
could be as many as 32, depending on the input value. It's possible to
implement the same algorithm with significantly fewer branches, and no
backward branches.

Optimized Implementation
------------------------

An alternative implementation, taken by the following program (also in
`code/ffs.c`), treats the bits of the input word in chunks, allowing
sequences of zero bits to be skipped over more quickly.

``` {.c}
$include 19-26 code/ffs.c
```

However, this code is much less obvious than the previous
implementation. If it is correct, we would like to use it, since it
has the potential to be faster. But how do we gain confidence that it
calculates the same results as the original program?

SAWScript allows us to state this problem concisely, and to quickly
and automatically prove the equivalence of these two functions for all
possible inputs.

Buggy Implementation
--------------------

Finally, a buggy implementation which is correct on all but one
possible input (also in `code/ffs.c`). Although contrived, this
program represents a case where traditional testing -- as opposed
to verification -- is unlikely to be helpful.

``` {.c}
$include 29-33 code/ffs.c
```

SAWScript allows us to quickly identify an input exhibiting the bug.

Generating LLVM Code
--------------------

The SAWScript interpreter can analyze LLVM code, but most programs are
originally written in a higher-level language such as C, as in our
example. Therefore, the C code must be translated to LLVM, using
something like the following command:

    # clang -c -emit-llvm -o ffs.bc ffs.c

This command, and following command examples in this tutorial, can be
run from the `code` directory accompanying the tutorial document. A
`Makefile` also exists in that directory, providing quick shortcuts
for tasks like this. For instance, we can get the same effect as the
previous command by doing:

    # make ffs.bc

Equivalence Proof
-----------------

We now show how to use SAWScript to prove the equivalence of the
reference and implementation versions of the FFS algorithm, and
exhibit the bug in the buggy implementation.

A SAWScript program is typically structured as a sequence of commands,
potentially along with definitions of functions that abstract over
commonly-used combinations of commands.

The following script (in `code/ffs_llvm.saw`) is sufficient to
automatically prove the equivalence of the `ffs_ref` and `ffs_imp`
functions, and identify the bug in `ffs_bug`.

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
assertion of equality between two existing terms.  Arbitrary
Cryptol expressions can be embedded within SAWScript; to distinguish
Cryptol code from SAWScript commands, the Cryptol code is placed
within double brackets `{{` and `}}`.

The `prove_print` command can verify the validity of such an assertion, and
print out the results of verification. The `abc` parameter indicates what
theorem prover to use; SAWScript offers support for many other SAT and
SMT solvers as well as user definable simplification tactics.

If the `saw` executable is in your PATH, you can run the script above with

    # saw ffs_llvm.saw

producing the output

```
Loading module Cryptol
Loading file "ffs_llvm.saw"
Extracting reference term
Extracting implementation term
Extracting buggy term
Proving equivalence
Valid
Finding bug via sat search
Sat: 1052688
Finding bug via failed proof
Invalid: 1052688
Done.
```

Note that `0x101010 = 1052688`, and so both explicitly searching for
an input exhibiting the bug (with `sat`) and attempting to prove the
false equivalence (with `prove`) exhibit the bug. Symmetrically, we
could use `sat` to prove the equivalence of `ffs_ref` and `ffs_imp`,
by checking that the corresponding disequality is
unsatisfiable. Indeed, this exactly what happens behind the scenes:
`prove abc <goal>` is essentially `not (sat abc (not <goal>))`.

Cross-Language Proofs
---------------------

We can implement the FFS algorithm in Java with code almost identical
to the C version.

The reference version (in `code/FFS.java`) uses a loop, like the C
version:

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

    # javac -g FFS.java

Now we can do the proof both within and across languages (from
`code/ffs_compare.saw`):

```
$include all code/ffs_compare.saw
```

We can run this with the `-j` flag to tell it where to find the Java
standard libraries:

    # saw -j <path to rt.jar or classes.jar from JDK> ffs_compare.saw

Using SMT-Lib Solvers
=====================

The examples presented so far have used the internal proof system
provided by SAWScript, based primarily on a version of the ABC tool
from UC Berkeley linked into the `saw` executable. However, there is
internal support for other proof tools -- such as Yices and CVC4 as
illustrated in the next example -- and more general support for
exporting models representing theorems as goals in the SMT-Lib
language. These exported goals can then be solved using an external
SMT solver.

Consider the following C file:

``` {.c}
$include all code/double.c
```

In this trivial example, an integer can be doubled either using
multiplication or shifting. The following SAWScript program
(`code/double.saw`) verifies that the two are equivalent using both
internal ABC, Yices, and CVC4 modes,
and by exporting an SMT-Lib theorem to be checked later, by an external
SAT solver.

```
$include all code/double.saw
```

The new primitives introduced here are the tilde operator, `~`, which
constructs the logical negation of a term, and `write_smtlib2`, which
writes a term as a proof obligation in SMT-Lib version 2 format.
Because SMT solvers are satisfiability solvers, negating the input
term allows us to interpret a result of "unsatisfiable" from the
solver as an indication of the validity of the term. The `prove`
primitive does this automatically, but for flexibility the
`write_smtlib2` primitive passes the given term through unchanged,
because it might be used for either satisfiability or validity
checking.

The SMT-Lib export capabilities in SAWScript make use of the Haskell
SBV package, and support ABC, Boolector, CVC4, MathSAT, Yices, and Z3.


External SAT Solvers
====================

In addition to the `abc`, `cvc4`, and `yices` proof tactics used above,
SAWScript can also invoke arbitrary
external SAT solvers that support the DIMACS
CNF format for problem and solution descriptions, using the
`external_cnf_solver` tactic. For example, you can use PicoSAT to
prove the theorem `thm` from the last example, with the following commands:

    let picosat = external_cnf_solver "picosat" ["%f"];
    prove_print picosat thm;

The use of `let` is simply a convenient abbreviation. The following
would be equivalent:

    prove_print (external_cnf_solver "picosat" ["%f"]) thm;

The first argument to `external_cnf_solver` is the name of the
executable. It can be a fully-qualified name, or simply the bare
executable name if it's in your PATH. The second argument is an array
of command-line arguments to the solver. Any occurrence of `%f` is
replaced with the name of the temporary file containing the CNF
representation of the term you're proving.

The `external_cnf_solver` tactic is based on the same underlying
infrastructure as the `abc` tactic, and is generally capable of
proving the same variety of theorems.

Compositional Proofs
====================

The examples shown so far treat programs as monolithic entities. A
Java method or C function, along with all of its callees, is
translated into a single mathematical model. SAWScript also has
support for more compositional proofs, as well as proofs about
functions that use heap data structures.

<!--
Compositional Cryptol Proofs
----------------------------

The simplest form of compositional reasoning within SAWScript involves
treating sub-terms of models as uninterpreted functions.

TODO
-->

Compositional Imperative Proofs
-------------------------------

As a simple example of compositional reasoning on imperative programs,
consider the following Java code.

``` {.java}
$include all code/Add.java
```

Here, the `add` function computes the sum of its arguments. The `dbl`
function then calls `add` to double its argument. While it would be easy
to prove that `dbl` doubles its argument by following the call to `add`,
it's also possible in SAWScript to prove something about `add` first,
and then use the results of that proof in the proof of `dbl`, as in the
following SAWScript code (`code/java_add.saw`).

````
$include all code/java_add.saw
````

This can be run as follows:

    # saw -j <path to rt.jar or classes.jar from JDK> java_add.saw

In this example, the definitions of `add_spec` and `dbl_spec` provide
extra information about how to configure the symbolic simulator when
analyzing Java code. In this case, the setup blocks provide explicit
descriptions of the implicit configuration used by `java_extract`
(used in the earlier Java FFS example and in the next section). The
`java_var` commands instruct the simulator to create fresh symbolic
inputs to correspond to the Java variables `x` and `y`. Then, the
`java_return` commands indicate the expected return value of the each
method, in terms of existing models (which can be written inline).

Finally, the `java_verify_tactic` command indicates what method to use
to prove that the Java methods do indeed return the expected value. In
this case, we use ABC.

To make use of these setup blocks, the `java_verify` command analyzes
the method corresponding to the class and method name provided, using
the setup block passed in as a parameter. It then returns an object that
describes the proof it has just performed. This object can be passed
into later instances of `java_verify` to indicate that calls to the
analyzed method do not need to be followed, and the previous proof about
that method can be used instead of re-analyzing it.

Interactive Interpreter
=======================

The examples so far have used SAWScript in batch mode on complete
script files. It also has an interactive Read-Eval-Print Loop (REPL)
which can be convenient for experimentation. To start the REPL, run
SAWScript with no arguments:

    # saw

The REPL can evaluate any command that would appear at the top level
of a standalone script, or in the `main` function, as well as a few
special commands that start with a colon:

    :env     display the current sawscript environment
    :type    check the type of an expression
    :browse  display the current environment
    :eval    evaluate an expression and print the result
    :?       display a brief description about a built-in operator
    :help    display a brief description about a built-in operator
    :quit    exit the REPL
    :load    load a module
    :add     load an additional module
    :cd      set the current working directory

As an example of the sort of interactive use that the REPL allows,
consider the file `code/NQueens.cry`, which provides an Cryptol
specification of the problem of placing a specific number of queens on
a chess board in such a way that none of them threaten any of the
others.

````
$include 21-56 code/NQueens.cry
````

This example gives us the opportunity to use the satisfiability
checking capabilities of SAWScript on a problem other than
equivalence verification.

First, we can load a model of the `nQueens` term from the Cryptol file.

    # saw
       ___  __ _ _ _ _
      / __|/ _' | | | |
      \__ \ (_| | | | |
      |___/\__,_|\_,_/

    sawscript> m <- cryptol_load "NQueens.cry"
    Loading module Cryptol
    Loading module Main
    sawscript> let nq8 = {{ m::nQueens`{8} }}

Once we've extracted this model, we can try it on a specific
configuration to see if it satisfies the property that none of the
queens threaten any of the others.

    sawscript> print {{ nq8 [0,1,2,3,4,5,6,7] }}
    False

This particular configuration didn't work, but we can use the
satisfiability checking tools to automatically find one that does.

    sawscript> sat_print abc nq8
    Sat [3,1,6,2,5,7,4,0]

And, finally, we can double-check that this is indeed a valid solution.

    sawscript> print (nq8 [3,1,6,2,5,7,4,0])
    True

More Sophisticated Imperative Models
====================================

The analysis of JVM and LLVM programs presented so far have been
relatively simple and automated. The `java_extract` and `llvm_extract`
commands can extract models from simple methods or functions with
minimal effort. For more complex code, however, more flexibility is
necessary.

The `java_symexec` and `llvm_symexec` commands provide greater control
over the use of symbolic execution to generate models of JVM and LLVM
programs. These two commands have similar structure, but slight
differences due to the differences between the underlying languages.

The shared structure is intuitively the following: both commands take
parameters that set up the initial symbolic state of the program,
before execution begins, and parameters that indicate which portions
of the program state should be returned as output when execution
completes.

The initial state before symbolic execution typically includes unknown
(symbolic) elements. To construct `Term` inputs that contains symbolic
variables, you can start by using the `fresh_symbolic` command, which
takes a name and a type as arguments, and returns a `Term`. The name
is used only for pretty-printing, and the type is used for later
consistency checking. For example, consider the following command:

    x <- fresh_symbolic "x" {| [32] |};

This creates a new `Term` stored in the SAWScript variable `x` that is
a 32-bit symbolic word.

These symbolic variables are most commonly used by the more general
Java and LLVM model extraction commands. The Java version of the
command has the following signature:

    java_symexec : JavaClass
                -> String
                -> [(String, Term)]
                -> [String]
                -> TopLevel Term

This first two parameters are the same as for `java_extract`: the
class object and the name of the method from that class to execute.
The third parameter describes the initial state of execution. For each
element of this list, SAWScript writes the value of the `Term` to the
destination variable or field named by the `String`. Typically, the
`Term` will either be directly the result of `fresh_symbolic` or an
more complex expression containing such a result, though it is allowed
to be a constant value. The syntax of destination follows Java syntax.
For example, `o.f` describes field `f` of object `o`. The fourth
parameter indicates which elements of the final state to return as
output. The syntax of the strings in this list is the same as for the
initial state description.

An example of using `java_symexec` on a simple function (using just
scalar arguments and return values) appears in the
`code/java_symexec.saw` file, quoted below.

```
$include all code/java_symexec.saw
```

This script uses `fresh_symbolic` to construct two fresh variables,
`x` and `y`, and then passes them in as the initial values of the
method parameters of the same name. It then uses the special name
`return` to refer to the return value of the method in the output
list. Finally, it uses the `abstract_symbolic` command to convert a
`Term` containing symbolic variables into a function that takes the
values of those variables as parameters. This last step exists partly
to illustrate the use of `abstract_symbolic`, and partly because the
`prove_print` command currently cannot process terms that contain
symbolic variables (though we plan to adapt it to be able to in the
near future).

The LLVM version of the command has some additional complexities, due
to the less structured nature of the LLVM memory model.

    llvm_symexec : LLVMModule
                -> String
                -> [(String, Int)]
                -> [(String, Term, Int)]
                -> [(String, Int)]
                -> TopLevel Term

Symmetrically with the Java version, the first two arguments are the
same as for `llvm_extract`. However, while the Java version of this
command takes two additional arguments, the LLVM version takes three.
The first list describes allocations, the second describes initial
values, and the third describes results. For the first list, SAWScript
will initialize the pointer named by the given string to point to the
number of elements indicated by the `Int`. For the second list,
SAWScript will write to the given location with the given number of
elements read from the given term. The name given in the initial
assignment list should be written as an r-value, so if `"p"` appears
in the allocation list then `"*p"` should appear in the initial
assignment list. Finally, the third list describes the results, using
the same convention: read $n$ elements from the named location.

The numbers given for a particular location in the three lists need
not be the same. For instance, we might allocate 10 elements for
pointer `p`, write 8 elements to `*p` at the beginning, and read 4
elements from `*p` at the end. However, both the initialization and
result sizes must be less than or equal to the allocation size.

An example of using `java_symexec` on a function similar to the Java
method just discussed appears in the `code/java_symexec.saw` file,
quoted below.

```
$include all code/llvm_symexec.saw
```

This has largely the same structure as the Java example, except that
`llvm_symexec` command takes and extra argument, describing
allocations, and the input and output descriptions take sizes as well
as values, to compensate for the fact that LLVM does not track how
much memory a given variable takes up. In simple scalar cases such as
this one, the size argument will always be `1`. However, if an input
or output parameter is an array, it will take on the corresponding
size value. For instance, say an LLVM function takes as a parameter an
array `a` containing 10 elements of type `uint32_t *`, which it reads
and writes. We could then call `llvm_symexec` with an allocation
argument of `[("a", 10)]`, and both input and output arguments of
`[("*a", 10)]` (note the additional `*` in the latter).

Other Examples
==============

The `code` directory contains a few additional examples not mentioned
so far. These remaining examples don't cover significant new material,
but help fill in some extra use cases that are similar, but not
identical to those already covered.

Java Equivalence Checking
-------------------------

The previous examples showed comparison between two different LLVM
implementations, and cross-language comparisons between Cryptol, Java,
and LLVM. The script in `code/ffs_java.saw` compares two different
Java implementations, instead.

````
$include all code/ffs_java.saw
````

As with previous Java examples, this one needs to be run with the `-j`
flag to tell the interpreter where to find the Java standard
libraries.

    # saw -j <path to rt.jar or classes.jar from JDK> ffs_java.saw

AIG Export and Import
---------------------

Most of the previous examples have used the `abc` tactic to discharge
theorems. This tactic works by translating the given term to
And-Inverter Graph (AIG) format, transforming the graph in various
ways, and then using a SAT solver to complete the proof.

Alternatively, the `write_aig` command can be used to write an AIG
directly to a file, for later processing by external tools, as shown
in `code/ffs_gen_aig.saw`.

````
$include all code/ffs_gen_aig.saw
````

Conversely, the `read_aig` command can construct an internal term from
an existing AIG file, as shown in `code/ffs_compare_aig.saw`.

````
$include all code/ffs_compare_aig.saw
````

Both of these scripts can be run by `saw` with no arguments (though
the latter must be run second, because it uses files generated by the
former):

    # saw ffs_gen_aig.saw

    # saw ffs_compare_aig.saw

<!---

Reference
=========

Importing External Models
-------------------------

`read_aig`
`read_sbv`
`read_core`

Exporting SAWCore Models
------------------------

`write_aig`
`write_smtlib1`
`write_smtlib2`
`write_core`

Constructing Model Terms
------------------------

```
reverse            : {n, a} [n]a -> [n]a;

eq                 : {a} a -> a -> Bit;
ite                : {a} Bit -> a -> a -> a;

not                : Bit -> Bit;
conj               : Bit -> Bit -> Bit;
disj               : Bit -> Bit -> Bit;

get                : {n, a} [n]a -> Fin -> a;
set                : {n, a} [n]a -> Fin -> a -> [n]a;

bvEq               : {n} [n] -> [n] -> Bit;
bvNot              : {n} [n] -> [n];
bvAdd              : {n} [n] -> [n] -> [n];
bvSub              : {n} [n] -> [n] -> [n];
bvMul              : {n} [n] -> [n] -> [n];
bvAnd              : {n} [n] -> [n] -> [n];
bvOr               : {n} [n] -> [n] -> [n];
bvXor              : {n} [n] -> [n] -> [n];
bvShl              : {n} [n] -> Int -> [n];
bvShr              : {n} [n] -> Int -> [n];

bvuge              : {n} [n] -> [n] -> Bit;
bvugt              : {n} [n] -> [n] -> Bit;
bvule              : {n} [n] -> [n] -> Bit;
bvult              : {n} [n] -> [n] -> Bit;
bvsge              : {n} [n] -> [n] -> Bit;
bvsgt              : {n} [n] -> [n] -> Bit;
bvsle              : {n} [n] -> [n] -> Bit;
bvslt              : {n} [n] -> [n] -> Bit;

finval             : Int -> Int -> Fin;

join               : {m, n, o, a} [m][n]a -> [o]a;
split              : {m, n, o, a} [m]a -> [n][o]a;
trunc              : {m, n} Int -> [m] -> [n];
sext               : {m, n} Int -> [m] -> [n];
uext               : {m, n} Int -> [m] -> [n];
```

Running Provers
---------------

`prove`
`prove_print`
`sat`
`sat_print`

`caseProofResult`
`caseSatResult`

`simplify`
`print_goal`
`unfolding`

`abc`
`yices`

TODO: implement the following
`cnf_solver`
`qbf_solver`
`smtlib1_solver`
`smtlib2_solver`

Extracting Models from Programs
-------------------------------

**Cryptol**

`cryptol_module`
`cryptol_extract`

**Java**

**LLVM**

**Extra Proof Tactics**

`offline_aig`
`offline_smtlib1`
`offline_smtlib2`
`offline_extcore`

Transforming Models
-------------------

`rewrite`
`empty_ss`
`basic_ss`
`addsimp`

Miscellaneous
-------------

`print`
`print_term`
`print_type`
`show_term`
`term_size`
`term_tree_size`

-->
