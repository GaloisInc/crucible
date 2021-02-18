This is a grammar-based test generator, designed for use with Crux.
You write a grammar describing the kinds of test cases you want to generate,
and the tool produces a list of strings that satisfy the grammar.

# Grammar definitions

The tool accepts context-free grammars, with a few extensions described below.
A grammar is defined by a list of productions, where the left-hand side of each
production is a single nonterminal, and the right-hand side is a string that
may contain nonterminals.
The generator starts with the `<<start>>` nonterminal and produces every legal
expansion according to the productions in the grammar.

Here is a trivial grammar with two productions:

```
// The RHS can either be a single line...
start ::= a single-line production

// or an indented block.
start ::=
    a
    multi-line
    production
```

Running the generator on this grammar produces the outputs

```
a single-line production
```

and 

```
a
multi-line
production
```

using the two different productions for `start` given in the grammar.

Nonterminals on the right-hand side are written inside double angle brackets:

```
start ::= <<X>> <<X>>
X ::= A
X ::= B
```

This produces the four outputs `A A`, `A B`, `B A`, and `B B`, as each instance
of `<<X>>` can be expanded in two different ways.

A nonterminal with no matching productions fails to expand, producing no
output:

```
start ::= A
start ::= B <<bad>>
// No productions for `bad`
```

This produces only the single output `A`, as there is no way to satisfy the
`bad` nonterminal in the RHS of the second `start` production.


## Type arguments

Nonterminals can have arguments.
These are typically used to represent types in the target programming language,
making it easier to define a grammar that only produces well-typed expressions,
though the generator itself makes no assumptions about the meanings of the
arguments.
A nonterminal with arguments can only be expanded using a production with
matching arguments.

Here is an example:

```
start ::=
    f(<<expr[int]>>)
    g(<<expr[str]>>)

expr[int] ::= 0
expr[str] ::= "hello"
```

This produces:

```
f(0)
g("hello")
```

Types themselves can have type arguments, which is useful for representing
generic types in the target language.  For example, `expr[array[int]]` is a
valid nonterminal.

Nonterminals and types can have multiple comma-separated arguments, as in
`foo[int, map[int, str]]`.


## Generic productions

Productions can be generic over type arguments.
This is useful for dealing with generic types in the target language.
For example:

```
start ::=
    <<expr[array[int]]>>
    <<expr[array[str]]>>

expr[int] ::= 0
expr[str] ::= "hello"
// A generic production
for[T] expr[array[T]] ::= [<<expr[T]>>, <<expr[T]>>, <<expr[T]>>]
```

This produces:

```
[0, 0, 0]
["hello", "hello", "hello"]
```

In the third `expr` production, the `for[T]` clause declares that the
production applies for all type arguments `T`.
Then the variable `T` can appear anywhere in the LHS or RHS of the production.

For generic productions, the nonterminal being expanded is matched against the
LHS of the production by unification.
In particular, this permits the same variable to appear more than once in the
LHS.
For example, `for[T] bar[T, T] ::= ...` applies to the nonterminal `bar[A, B]`,
as long as `A` unifies with `B`.

A variable can also appear zero times in the LHS.
This is useful for productions where the RHS needs to be internally consistent,
but need not be consistent with any part of the surrounding context.
For example:

```
// Produce an expression of type `U` by applying a function of type `T -> U` to
// an argument of type `T`.
for[T, U] expr[U] ::= <<function[T, U]>>(<<expr[T]>>)
```


## Builtins

The tool provides built-in productions for certain nonterminals, which support
functionality that would not be easy to express in an ordinary grammar.

Note that many builtins have side effects on the expansion state.
The order in which builtins are expanded can thus affect the output.
By default, nonterminals in the RHS of a production are expanded in the order
they appear, proceeding depth-first.
However, the order can be controlled using modifiers described in the
[expansion order](#expansion-order) section below.

### Cost budgets

Many constructs in real programming languages are unbounded; for example, a
function can usually contain arbitrarily many statements.
In test generation, it's necessary to set limits on these constructs to avoid
generating infinitely many uninteresting test cases.
To support this, the tool provides builtins for setting budget counters, which
can limit the use of certain productions.

For example:

```
start ::= <<set_budget[stmts, 3]>><<stmts>>

// A list of statements is either empty...
stmts ::=
// Or a statement followed by a list of statements.  However, this second rule
// can only be used as long as there is remaining budget.
stmts ::=
    <<take_budget[stmts, 1]>><<stmt>>
    <<stmts>>

stmt ::= print("Hello, World!")
```

This produces four outputs, consisting of 0, 1, 2, or 3 copies of the statement
`print("Hello, World!")`.
Outputs with four or more statements are forbidden because the `take_budget`
nonterminal in the second `stmts` production fails to expand once the
three-statement budget (set in the `start` production) has been exhausted.

In more detail, the budget system provides these nonterminals:

 * `set_budget[name, amount]`: Sets the current budget counter for `name` to
   `amount` (which must be a non-negative integer), and expands to the empty
   string.

 * `add_budget[name, amount]`: Adds `amount` (a non-negative integer) to the
   current budget counter for `name`, and expands to the empty string.

 * `take_budget[name, amount]`: Tries to subtract `amount` (a non-negative
   integer) from the current budget counter for `name`.  If this would cause
   the counter to become negative, then `take_budget` fails to expand (just as
   if it were a nonterminal with no matching productions); otherwise, it
   expands to the empty string.

 * `check_budget[name, amount]`: Checks that the budget counter for `name` is
   exactly `amount`.  If so, it expands to the empty string; otherwise, it
   fails to expand.  This is useful for requiring that the entire budget is
   spent during expansion, by adding a `check_budget[name, 0]` at the end of
   the top-level production.

### Locals

These builtins allow tracking the types of local variables (called simply
"locals", to avoid confusion with type variables) within the generated program.
This allows the grammar to generate well-typed programs where locals are always
initialized before being used.

For example:

```
start ::=
    <<fresh_local[int]>> = 1;
    f(<<expr[int]>>)

expr[int] ::= 0
for[T] expr[T] ::= <<choose_local[T]>>
```

This produces two outputs: `x0 = 1; f(0)` and `x0 = 1; f(x0)`.
The `fresh_local[int]` nonterminal declares a new local in the current scope,
gives it type `int`, and expands to its automatically-generated name.
`choose_local[int]` expands to the name of any declared local of type `int`.

If there are multiple variables of the correct type, `choose_local` can expand
multiple times, just as if it were a nonterminal with multiple productions:

```
start ::=
    <<fresh_local[int]>> = 0;
    <<fresh_local[int]>> = 1;
    f(<<choose_local[int]>>)
```

This produces both `x0 = 0; x1 = 1; f(x0)` and `x0 = 0; x1 = 1; f(x1)`.

Locals and scopes are manipulated using these nonterminals:

 * `fresh_local[T]`: Defines a new local of type `T` in the current scope and
   expands to its name.
 * `choose_local[T]`: Expands to the name of a variable of type `T` in any
   enclosing scope.  If there are multiple matching variables, then this
   nonterminal can expand to multiple outputs.
 * `take_local[T]`: Expands to the name of a variable of type `T` in any
   enclosing scope (like `choose_local[T]`), and removes the chosen variable
   from its scope, so it can't be chosen again.
 * `push_scope`: Push a new local scope onto the stack.  Locals defined with
   `fresh_local` are always added to the most recently pushed scope.
 * `pop_scope`: Pop the most recently pushed scope from the stack.  All locals
   defined in that scope are discarded, and can no longer be returned by
   `choose_local`.

The arguments to `fresh_local` and `choose_local` are handled by unification,
like arguments to ordinary generic productions.
In particular, this means the argument to `fresh_local` can be an unconstrained
unification variable, leaving the type of the local to be decided later.
For example:

```
start ::= <<body>>

for[T] body ::=
    <<fresh_local[T]>> = <<expr[T]>>;
    f(<<choose_local[int]>>)

expr[int] ::= 0
expr[str] ::= "hello"
```

This produces only one output: `x0 = 0; f(0)`.
`fresh_local[T]` expands to `x0` but leaves the type of that local
undetermined; `expr[T]` expands to either `0` (unifying `T = int`) or `"hello"`
(unifying `T = str`); and finally `choose_local[int]` expands successfully only
in the case where `T = int`.

### Recursive expansion

These builtins recursively invoke the grammar expander.
This is an advanced feature that is rarely needed.

 * `expand_all[nt]`: Take every expansion of the nonterminal `nt` that is legal
   in this context, and concatenate them together.

   For example, this can be used to produce a list of expressions for the
   generated test to evaluate at run time:

   ```
   expr[int] ::= 0
   expr[int] ::= 1
   for[T] expr[T] ::= <<choose_local[T]>>

   for[T] expr_comma[T] ::= <<expr[T]>>,

   all_ints ::= [<<expand_all[expr_comma[int]]>>]
   ```

   In a scope with two locals of type `int` named `x1` and `x2`, `all_ints`
   would expand to `[0,1,x1,x2,]`.

 * `expand_first[nt]`: Take the first expansion of the nonterminal `nt` that is
   legal in this context.  If `nt` fails to expand here, `expand_first[nt]`
   also fails to expand.

   For example, given these declarations:

   ```
   foo ::= A
   foo ::= B
   ```

   `foo` can expand to either `A` or `B`, while `expand_first[foo]` expands
   only to `A`.

The interactions between recursive expansion and type variable unification are
somewhat complex.
See the comments in [`lib.rs`](src/lib.rs), `fn add_builtin_expand` for the
complete details.

### Miscellaneous

 * `ctor_name[T]`: Expands to the topmost "type constructor name" of the
   argument `T`.  For example, `ctor_name[array[int]]` expands to `array`.

 * `expansion_counter`: Expands to an integer indicating the index of the
   current expansion.  That is, this expands to `0` in the first output, `1` in
   the second output, and so on.  This is useful for assigning a unique name to
   each generated test case.


## Expansion order

Some builtins have side effects on the expansion state when they are expanded,
which means the order of expansion of builtins can affect the output.
Expansion always proceeds depth-first, with each nonterminal being fully,
recursively expanded before its remaining siblings are processed; however, the
order of expansion of siblings within a single production's RHS can be altered
by applying modifiers to the nonterminals.

The supported modifiers are `^` (expand early) and `$` (expand late).
These do not affect the output string, only the order in which nonterminals are
processed.
For example:

```
start ::= good <<first>> <<second>>
start ::= bad <<second>> <<first>>
start ::= fixed <<second>> <<^first>>

// `first` must be expanded before `second`, otherwise `take_budget` will fail
first ::= first<<set_budget[x, 1]>>
second ::= second<<take_budget[x, 1]>>
```

This produces two outputs, `good first second` and `fixed second first`.
The `good` production expands `first` then `second`, and succeeds; `bad`
expands `second` first, and fails.
The `fixed` production succeeds because the `first` nonterminal, despite
appearing later in the RHS, is expanded early due to the `^` modifier, and the
`second` nonterminal is expanded afterward.

Specifically, order of expansion when accounting for modifiers is to expand all
early nonterminals (`^` modifier) in the order of their appearance in the RHS,
then expand all normal nonterminals (no modifier) in order of appearance, and
finally expand all late nonterminals (`$` modifier) in order of appearance.

Expansion order modifiers is particularly important when dealing with local
declarations.
Consider this naïve approach:

```
start ::=
    <<fresh_local[int]>> = <<expr[int]>>

expr[int] ::= 0
for[T] expr[T] ::= <<choose_local[int]>>
```

This can produce the nonsensical declaration `x0 = x0`, as `fresh_local[int]`
is expanded first, allowing `x0` to be chosen by `choose_local` within the
second `expr` production.
This can be prevented by expanding the `fresh_local` nonterminal late:

```
start ::=
    <<$fresh_local[int]>> = <<expr[int]>>

expr[int] ::= 0
for[T] expr[T] ::= <<choose_local[int]>>
```

This now produces only `x0 = 0`, as desired.
