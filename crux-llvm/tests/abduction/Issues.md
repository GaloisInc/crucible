### The Goal 
What4 has a `get-abduct` command using cvc5, that given a goal that is disproved by the SMT solver (negation satisfiable), returns an abduct - a formula that entails the goal. We want to integrate abduction with online solving in crux. As a first attempt, we do the following. From the proof annotations (and the implicit goals) in a C file, crux creates a proof goal tree, a tree with a proof goal in each node. It traverses this tree and queries the SMT solver with the goal. If the query is unsatisfiable, the goal is successfully proved, if its satisfiable, the solver's counter-example is interpreted and output. We ask for and print one abduct in addition to the counter-example.

### Test Files
We have 9 test files over C ints, all unprovable:
1. `abdpaper` the running example from the cvc5 abduction paper: does `y > 0 |= x + y + z > 0`? Acceptable abduct: `x + z > 0`.
2. `addident`: does `|= x + y == x`? Acceptable abduct: `y = 0`.
3. `addinv`: does `|= x + y == x`? Acceptable abduct: `y = -x`.
4. `andex`: does `|= x & y == 1`? Acceptable abduct: `x = 1 ^ y = 1`.
5. `file` from a crux-llvm example: does `x < 100 |= x + 1 < 100`? Acceptable abduct: `x < 99`.
6. `maxint`: does `|= x + 1 > x`? Acceptable abduct: `x < maxint`.
7. `multident`: does `|= x * y == x`? Acceptable abduct: `y = 1`.
8. `multinv`: does `|= x * y == 0`? Acceptable abduct: `y = 0`.
9. `trans`: does `x > y |= x > z`? Acceptable abduct: `y > z`.

### Test Results

| Test       | Entailment                  | Baseline           | 8-bit Abducts                   | 32-bit Abducts          | Notes                                        |
|------------|-----------------------------|--------------------|---------------------------------|-------------------------|----------------------------------------------|
| abdpaper   | `y > 0 \|= x + y + z > 0`   | `x + z > 0`        | `(= (bvshl z x) x))`            | `(bvult (bvadd x z) 1)` |                                              |
|            |                             |                    | `(= (bvadd x z) 0)`             | Timeout                 |                                              |
|            |                             |                    | Timeout                         | Timeout                 |                                              |
| addident   | `\|= x + y == x`            | `y = 0`            | `(bvult y 1)`                   | `(bvult y 1)`           | both: what4 rewrites as `y = 0`, removes `x` |
|            |                             |                    | Timeout                         | Timeout                 |                                              |
|            |                             |                    | Timeout                         | Timeout                 |                                              |
| addinv     | `\|= x + y == x`            | `y = -x`           | `(= (bvshl y x) x)`             | `(= (bvshl y x) x)`     | both: what4 rewrites as `-y = x`             |
|            |                             |                    | `(= (bvneg y) x)`               | `(= (bvneg y) x)`       |                                              |
|            |                             |                    | Timeout                         | Timeout                 |                                              |
| andex      | `x = 1 \|= x & y == 1`      | `x = 1 ^ y = 1`    | `(= y 1)`                       | `(= y 1)`               |                                              |
|            |                             |                    | `(bvult 0 (bvand y 1))`         | `(= (bvnot 0) y)`       |                                              |
|            |                             |                    | Timeout                         | `(= (bvor 1 y) y)`      |                                              |
| file       | `x < 100 \|= x + 1 < 100`   | `x < 99`           | `(= 0 x)`                       | `(= 0 x)`               |                                              |
|            |                             |                    | `(= 1 x)`                       | `(= x 1)`               |                                              |
|            |                             |                    | `(bvult 100 x)`                 | `(bvult 100 x)`         |                                              |
| maxint     | `\|= x + 1 > x`             | `x < maxint`       | `(= 0 x)`                       | `(= 0 x)`               |                                              |
|            |                             |                    | `(= x 1)`                       | `(= x 1)`               |                                              |
|            |                             |                    | `(bvult x 255)`                 | `(bvult x 4294967295)`  |                                              |
| multident  | `\|= x * y == x`            | `y = 1`            | `(= x 0)`                       | `(= x 0)`               |                                              |
|            |                             |                    | `(= 1 y)`                       | `(= 1 y)`               |                                              |
|            |                             |                    | `(= (bvmul x y) x)`             | Timeout                 |                                              |
| multinv    | `\|= x * y == x`            | `y = 0`            | `(= x 0)`                       | `(= x 0)`               |                                              |
|            |                             |                    | `(= y 0)`                       | `(= y 0)`               |                                              |
|            |                             |                    | `(bvult (bvmul y x) 1)`         | `(bvult (bvmul y x) 1)` |                                              |
| trans      | `x > y \|= x > z`           | `y > z`            | `(= y z)`                       | `(= y z)`               |                                              |
|            |                             |                    | `(= (bvor 1 z) y)`              | `(= (bvor 1 z) y)`      |                                              |
|            |                             |                    | `(= (bvadd 1 z) x)`             | `(= (bvadd 1 z) x)`     |                                              |

To-do:
* What do the what4 rewrites do to the abducts?
* We ask the abduction tactic for `n` abducts and it either passes or fails, it doesnt have a mode where it can give abducts incrementally. Add one.

### Issues
1. When `global-assertions` is turned on, cvc5 doesn't unfold `define-fun`s before adding them to the grammar. That is the abduction grammar is a over defined variables rather than the variables from the program. We had this patched by the cvc5 developers.
2. cvc5 considers abduction and unsat-cores incompatible. Crux has unsat core mode turned on by default and in its online solving mode, it asks for unsat cores if the solver returns unsat. In many of the example problems, some of the implicit goals make the solver return unsat and `get-unsat-core` is called. To make these two modes incompatible is unexpected behavior from cvc5, so the ultimate goal is to have them patch it. I have already brought it to the cvc5 developer's attention, and they have offered a patch, but the patch only works partially. Now the options can be turned on together (and I believe that) cvc5 wont throw an error if we call the `get-abduct` command and the `get-unsat-core` command not more than once each. Temporary solution: modify crux to not ask for unsat cores (implemented). (cvc5 developer fix is ready to be merged)
3. cvc5 emits the following parse error which we need to ask the developers about: "Overloaded constants must be type cast". For example, `/smtFiles8bitCvc5/test-andex-8-abd.smt2`. (cvc5 developer fix is ready to be merged)
4. (Potential) Issues:
    * Pretty printing abducts in C syntax?
    * LLVM icmp returns a bool which crux/crucible turns into a 1 bit BV and then pads it using an ITE. If this is done automatically, perhaps we would benefit from replacing this whole thing by a much simpler translation of this construct, one that avoids all the (potentially) unnecessary padding and ITEs.

### File Structure
- The C files for the 8-bit integer version of these examples are in `cFiles8bit/` and those for the 32-bit integer version are in `cFiles32bit/`.
- `smtFiles8bitCvc4/` and `smtFiles32bitCvc4/` contain the SMT files generated by the unmodified version of crux when it solves these examples without any abduction queries using cvc4 (for 8 and 32 bit integers, respectively).
- `smtFiles8bitCvc5/` and `smtFiles32bitCvc5/` contain the SMT files generated by crux using cvc5 with abduction queries made in the sat case.
- `smtFiles8bitCvc5Rwr/` contains hand-written SMT files representing the baseline - this is what I imagine the queries corresponding to the example C files would like like. 
