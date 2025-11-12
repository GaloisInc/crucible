# Crucible Overview

References to Crucible modules should all start with `Lang.Crucible`, which
we omit for brevity.

## Types

The types of the Crucible language are defined in `Types`.
  Of interest:
    * `CrucibleType` is the list of types
    * `TypeRepr` is the datatype of types, used when we want to store or pass
      around Crucible types.


## Values

The inhabitants of each type are specified via the type function `RegValue`
(`Simulator.RegValue`).  We also have `RegValue'` which is just
a newtype wrapper `RegValue`, so that we can partially apply it.

An important subset of the Crucible types are the base types (see `BaseToType`),
which is a backend specific type for the symbolic expression we can construct
(see `SymExpr` in `what4`).  Only these types may contain variables.
In practice, we only have one backend, namely `ExprBuidler` defined in `what4`,
(`What4.Expr.Builder`) which uses `what4`'s `Expr` as the type of symbolic
expressions.

Also, in some cases we use `RegEntry` (`Simulator.RegMap`) which
is just a pair of `RegValue` and it's associated `TypeRepr`.

There's also `BaseTerm` (`CFG.Expr`), which is similar to `RegEntry` but
for base types---it contains a `BaseTypeRepr` and a value of the corresponding
base type.  XXX: It is actually parameterized, so that it could be used with other
things than values, but I am not sure if this generality is used.


## Programs

The program executed by the simulator is in the form of a control flow
graph (CFG).   A typical way to construct them is as follows:

  1. use the functions in `CFG.Generator` to produce a CFG with 
     assignments (`CFG.Reg`)
  2. use `CFG.SSAConversion` to translate this to a CFG without assignments
     (`CFG.Core`)

Each of `CFG.Core` and `CFG.Reg` defines its own types for block statements,
`Stmt`, and terminator statement `TermStmt`.

The expression language for `CFG.Core` is the type `App` in `CFG.Expr`.



## The Symbolic Simulator

The state of a running simulator is described in `Simulator.ExecutionTree`:
  * `ExecState` is the current state of execution.
     We start with `InitialState`, and keep performing steps until we get
     to a `ResultState`.
  * As the simulator executes, it keeps track of its state in `SimState`.
  * `SimContext` is the part of the state that persists across branches
    (e.g, after we explore the `then` part of an `if` statement, we'll
    roll back some of the state changes before simulating the `else` part,
    but the stuff in `SimContexts` persists).  An important part of the
    `SymContext` is the simulator's backend (`Backend`), which is how the
    simulator communicates with a solver, and builds symbolic expressions.

To evaluate a CFG (`CFG.Core`) we evaluate the statements as described in
`Simualtor.EvalStmt` (`stepStmt`, `stepTerm`).   Evaluation of expressions
is described by `evalApp` in `Simulator.Evaluation`.

A lot of useful functionality relevant to the simulator can be accessed
from module `Simulator`.

The simulator supports mutable global variables.  Our tools use one such
global to store a language specific memory model.  For example, our LLVM
frontend is in `crucible-llvm`, the memory model is in `LLVM.MemModel` (with
more modules in `LLVM.MemModel.*`), and the function that makes the global
variable that contains the memory model is `LLVM.MemModel.mkMemVar`.
