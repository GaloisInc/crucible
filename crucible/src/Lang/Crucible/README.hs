{- | This module is only for documentation purposes, and provides a high
level overview of Crucible aimed at developers. -}
{-# OPTIONS_GHC -Wno-unused-imports #-}
module Lang.Crucible.README where

import What4.Interface
import What4.Expr.App
import What4.BaseTypes
import Lang.Crucible.Backend

import Lang.Crucible.Types
import Lang.Crucible.CFG.Expr
import Lang.Crucible.CFG.Core hiding (Expr)
import Lang.Crucible.CFG.SSAConversion

import Lang.Crucible.Simulator.RegValue
import Lang.Crucible.Simulator.RegMap
import Lang.Crucible.Simulator.ExecutionTree
import Lang.Crucible.Simulator.EvalStmt
import Lang.Crucible.Simulator.Evaluation
import Lang.Crucible.Simulator.Intrinsics



-- * Crucible Types

{- $
The types of the Crucible language are defined in "Lang.Crucible.Types".
Types are encoded using [singletons](https://github.com/Galoisinc/parameterized-utils?tab=readme-ov-file#parameterized-types-motivation):

* 'CrucibleType' is the Haskell type-level description of all Crucible types
* 'TypeRepr' are the associated value-level singletons, which
  are used when we pass around types, or store them in data structures.
-}

-- * Crucible Values

{- $
The inhabitants of each type are specified via the type function 'RegValue'.
We also have 'RegValue'' which is just a newtype wrapper around `RegValue`,
because in Haskell type families may not be partially applied but `newtypes` can.

An important subset of the Crucible types are the base types (see 'BaseToType'),
which is a backend specific type for the symbolic expression we can construct
(see 'SymExpr' in [what4](https://github.com/Galoisinc/what4)).
Only these types may contain variables. In practice, we always `what4`'s
'Expr' type to represent symbolic expressions.

Also, in some cases we use 'RegEntry' which
is just a pair of a 'RegValue' and it's associated 'TypeRepr'.

There's also 'BaseTerm', which is similar to 'RegEntry' but
for base types---it contains a `what4`'s 'BaseTypeRepr' and a value of the corresponding
base type (usually;  the type is parameterized on exactly what we package
with the type).
-}
  
-- * Crucible Programs
  
{- $
The program executed by the simulator is in the form of a control flow
graph (CFG).  A typical way to construct them is as follows:

  1. use the functions in "Lang.Crucible.CFG.Generator" to produce a CFG with 
     assignments ("Lang.Crucible.CFG.Reg")
  2. use 'toSSA' to translate this to a CFG without assignments
     ("Lang.Crucible.CFG.Core")

The core 'CFG' contains basic blocks with 'Stmt's and terminated
by 'TermStmt'.  The expression language for the core 'Core.CFG' is
the type 'App'.
-}
  
-- * Symbolic Simulator
  
{- $
The state of a running simulator is described in "Lang.Crucible.Simulator.ExecutionTree":

  * 'ExecState' is the current state of execution.
     We start with 'InitialState', and keep performing steps until we get
     to a 'ResultState'.
  * As the simulator executes, it keeps track of its state in 'SimState'.
  * 'SimContext' is the part of the state that persists across branches
    (e.g, after we explore the @then@ part of an @if2 statement, we'll
    roll back some of the state changes before simulating the @else@ part,
    but the stuff in `SimContexts` persists).  An important part of the
    'SimContext' is the simulator's backend (`_ctxBackend`), which is how the
    simulator communicates with a solver, and builds symbolic expressions
    ('IsSymBackend').


To evaluate a 'CFG' we evaluate the statements as described in
"Lang.Crucible.Simulator.EvalStmt" (details in 'stepStmt', 'stepTerm').
Details about expressions evaluation are in 'evalApp' in "Lang.Crucible.Simulator.Evaluation".

A lot of useful functionality relevant to the simulator can be accessed
from module "Lang.Crucible.Simulator".

The simulator supports mutable global variables.  Our tools use one such
global to store a language specific memory model, which records information
about various memory operations.
-}

-- * Intrinsics

{- $

Crucible type may be extended using 'IntrinsicType's.  An intrinsic type is
a type-level string, which can be given meaning by making an instance of
'IntrinsicClass'.
-}
  
