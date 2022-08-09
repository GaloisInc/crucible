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
Ran all experiments while keeping unsat cores internally off, since cvc5 wasn't able to produce abducts while unsat-cores was on:

| Test       | Entailment                | Baseline        | 8-bit Abducts           | Time          | 32-bit Abducts          | Time             | Notes                                        |
|------------|---------------------------|-----------------|-------------------------|---------------|-------------------------|------------------|----------------------------------------------|
| abdpaper   | `y > 0 \|= x + y + z > 0` | `x + z > 0`     | `(= (bvshl z x) x)`     | real	3m0.007s | `(bvult (bvadd x z) 1)` | real	3m0.003s  |                                              |
|            |                           |                 | `(= (bvadd x z) 0)`     | user	0m0.103s | Timeout                 | user	0m0.086s  |                                              |
|            |                           |                 | Timeout                 | sys	0m0.125s | Timeout                 | sys	0m0.053s  |                                              |
| addident   | `\|= x + y == x`          | `y = 0`         | `(bvult y 1)`           | real	3m0.006s | `(bvult y 1)`           | real	3m0.004s  | both: what4 rewrites as `y = 0`, removes `x` |
|            |                           |                 | Timeout                 | user	0m0.081s | Timeout                 | user	0m0.072s  |                                              |
|            |                           |                 | Timeout                 | sys	0m0.042s | Timeout                 | sys	0m0.059s  |                                              |
| addinv     | `\|= x + y == x`          | `y = -x`        | `(= (bvshl y x) x)`     | real	3m0.004s | `(= (bvshl y x) x)`     | real	3m0.003s  | both: what4 rewrites as `-y = x`             |
|            |                           |                 | `(= (bvneg y) x)`       | user	0m0.074s | `(= (bvneg y) x)`       | user	0m0.062s  |                                              |
|            |                           |                 | Timeout                 | sys	0m0.035s | Timeout                 | sys	0m0.052s  |                                              |
| andex      | `x = 1 \|= x & y == 1`    | `x = 1 ^ y = 1` | `(= y 1)`               | real	3m0.003s | `(= y 1)`               | real	0m1.166s  |                                              |
|            |                           |                 | `(bvult 0 (bvand y 1))` | user	0m0.045s | `(= (bvnot 0) y)`       | user	0m0.962s  |                                              |
|            |                           |                 | Timeout                 | sys	0m0.051s | `(= (bvor 1 y) y)`      | sys	0m0.132s  |                                              |
| file       | `x < 100 \|= x + 1 < 100` | `x < 99`        | `(= 0 x)`               | real	0m0.656s | `(= 0 x)`               | real	0m0.509s  |                                              |
|            |                           |                 | `(= 1 x)`               | user	0m0.383s | `(= x 1)`               | user	0m0.368s  |                                              |
|            |                           |                 | `(bvult 100 x)`         | sys	0m0.150s | `(bvult 100 x)`         | sys	0m0.109s  |                                              |
| maxint     | `\|= x + 1 > x`           | `x < maxint`    | `(= 0 x)`               | real	0m0.198s | `(= 0 x)`               | real	0m0.180s  |                                              |
|            |                           |                 | `(= x 1)`               | user	0m0.184s | `(= x 1)`               | user	0m0.157s  |                                              |
|            |                           |                 | `(bvult x 255)`         | sys	0m0.014s | `(bvult x 4294967295)`  | sys	0m0.023s  |                                              |
| multident  | `\|= x * y == x`          | `y = 1`         | `(= x 0)`               | real	0m5.171s | `(= x 0)`               | real	3m0.004s  |                                              |
|            |                           |                 | `(= 1 y)`               | user	0m4.903s | `(= 1 y)`               | user	0m0.081s  |                                              |
|            |                           |                 | `(= (bvmul x y) x)`     | sys	0m0.192s | Timeout                 | sys	0m0.022s  |                                              |
| multinv    | `\|= x * y == x`          | `y = 0`         | `(= x 0)`               | real	0m8.031s | `(= x 0)`               | real	1m41.755s |                                              |
|            |                           |                 | `(= y 0)`               | user	0m7.822s | `(= y 0)`               | user	1m41.285s |                                              |
|            |                           |                 | `(= (bvmul y x) 1)`     | sys	0m0.135s | `(bvult (bvmul y x) 1)` | sys	0m0.305s  |                                              |
| trans      | `x > y \|= x > z`         | `y > z`         | `(= y z)`               | real	0m1.386s | `(= y z)`               | real	0m1.944s  |                                              |
|            |                           |                 | `(= (bvor 1 z) y)`      | user	0m1.165s | `(= (bvor 1 z) y)`      | user	0m1.753s  |                                              |
|            |                           |                 | `(= (bvadd 1 z) x)`     | sys	0m0.144s | `(= (bvadd 1 z) x)`     | sys	0m0.123s  |                                              |

Repeated with a version of cvc5 where the unsat cores vs get-abduct bug was fixed so now we're getting abducts as well as unsat cores:

| Test       | Entailment                | Baseline        | 8-bit Abducts                 | Time             | 32-bit Abducts          | Time           | Notes                                        |
|------------|---------------------------|-----------------|-------------------------------|------------------|-------------------------|----------------|----------------------------------------------|
| abdpaper   | `y > 0 \|= x + y + z > 0` | `x + z > 0`     | `(= (bvneg x) z)`             | real	2m50.700s | `(= z 0)`               | real	3m0.003s |                                              |
|            |                           |                 | `(= (bvshl x (bvadd z y)) 1)` | user	2m50.396s | Timeout                 | user	0m0.046s |                                              |
|            |                           |                 | `(= (bvor x z) (bvshl x y))`  | sys	0m0.237s  | Timeout                 | sys	0m0.040s |                                              |
| addident   | `\|= x + y == x`          | `y = 0`         | `(bvult y 1)`                 | real	3m0.003s  | `(bvult y 1)`           | real	3m0.002s | both: what4 rewrites as `y = 0`, removes `x` |
|            |                           |                 | Timeout                       | user	0m0.042s  | Timeout                 | user	0m0.041s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.031s  | Timeout                 | sys	0m0.027s |                                              |
| addinv     | `\|= x + y == x`          | `y = -x`        | `(= (bvshl x y) y)`           | real	3m0.003s  | `(= (bvneg y) x)`       | real	3m0.002s | both: what4 rewrites as `-y = x`             |
|            |                           |                 | `(bvult (bvadd x y) 1)`       | user	0m0.058s  | Timeout                 | user	0m0.038s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.028s  | Timeout                 | sys	0m0.027s |                                              |
| andex      | `x = 1 \|= x & y == 1`    | `x = 1 ^ y = 1` | `(= 1 y)`                     | real	3m0.003s  | `(= y 1)`               | real	3m0.002s |                                              |
|            |                           |                 | `(bvult 0 (bvand y 1))`       | user	0m0.051s  | `(bvult 0 (bvand y 1))` | user	0m0.031s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.038s  | Timeout                 | sys	0m0.039s |                                              |
| file       | `x < 100 \|= x + 1 < 100` | `x < 99`        | `(bvult x 1)`                 | real	0m0.602s  | `(bvult x 1)`           | real	0m0.535s |                                              |
|            |                           |                 | `(bvult 100 x)`               | user	0m0.368s  | `(bvult 100 x)`         | user	0m0.337s |                                              |
|            |                           |                 | `(= 1 x)`                     | sys	0m0.106s  | `(= 1 x)`               | sys	0m0.125s |                                              |
| maxint     | `\|= x + 1 > x`           | `x < maxint`    | `(bvult x 1)`                 | real	3m0.003s  | `(bvult x 1)`           | real	3m0.002s |                                              |
|            |                           |                 | `(bvult x 255)`               | user	0m0.035s  | `(bvult x 4294967295)`  | user	0m0.042s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.023s  | Timeout                 | sys	0m0.021s |                                              |
| multident  | `\|= x * y == x`          | `y = 1`         | `(bvult x 1)`                 | real	0m5.141s  | N/A                     | N/A            | Crux times out on an implicit query          |
|            |                           |                 | `(= 1 y)`                     | user	0m4.855s  |                         | N/A            |                                              |
|            |                           |                 | `(= (bvsdiv x y) x)`          | sys	0m0.155s  |                         | N/A            |                                              |
| multinv    | `\|= x * y == x`          | `y = 0`         | `(= x 0)`                     | real	0m2.528s  | N/A                     | N/A            | Crux times out on an implicit query          |
|            |                           |                 | `(= y 0)`                     | user	0m2.308s  |                         | N/A            |                                              |
|            |                           |                 | `(= (bvmul y x) 0)`           | sys	0m0.108s  |                         | N/A            |                                              |
| trans      | `x > y \|= x > z`         | `y > z`         | `(= z y)`                     | real	0m7.979s  | `(= y z)`               | real	3m0.002s |                                              |
|            |                           |                 | `(= (bvashr x z) 1)`          | user	0m7.723s  | Timeout                 | user	0m0.030s |                                              |
|            |                           |                 | `(bvult z (bvlshr x y))`      | sys	0m0.126s  | Timeout                 | sys	0m0.041s |                                              |

Note that just turning on unsat cores (which is the only difference between the two versions of the tests for some files), slows down the abduction solver, and 
changes its abducts. For instance, the 32-bit version trans example, and both versions of the maxint example return 3 abducts almost immediately, with unsat-cores 
turned off but their counterparts are take the entire 3 minutes only because unsat cores are turned on.

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
- `smtFiles8bitCvc5Uc/` and `smtFiles32bitCvc5Uc/` contain the SMT files generated by crux using cvc5 with abduction queries made in the sat case, but also unsat cores turned on.
- `smtFiles8bitCvc5Rwr/` contains hand-written SMT files representing the baseline - this is what I imagine the queries corresponding to the example C files would like like. 
