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
With cvc5-1.0.2:
| Test       | Entailment                | Baseline        | 8-bit Abducts                 | Time             | 32-bit Abducts          | Time           | Notes                                        |
|------------|---------------------------|-----------------|-------------------------------|------------------|-------------------------|----------------|----------------------------------------------|
| abdpaper   | `y > 0 \|= x + y + z > 0` | `x + z > 0`     | `(= (bvsrem z x) x)`          | real	3m0.023s  | `(= 0 z)`               | real	3m0.003s |                                              |
|            |                           |                 | `(= (bvneg x) z)`             | user	0m0.112s  | `(bvult y (bvudiv z z))`| user	0m0.062s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.161s  | Timeout                 | sys	0m0.040s |                                              |
| addident   | `\|= x + y == x`          | `y = 0`         | `(bvult y 1)`                 | real	3m0.006s  | `(bvult y 1)`           | real	3m0.002s | both: what4 rewrites as `y = 0`, removes `x` |
|            |                           |                 | Timeout                       | user	0m0.069s  | Timeout                 | user	0m0.055s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.052s  | Timeout                 | sys	0m0.025s |                                              |
| addinv     | `\|= x + y == x`          | `y = -x`        | `(bvult (bvor x y) 1)`        | real	3m0.004s  | Timeout                 | real	3m0.002s | both: what4 rewrites as `-y = x`             |
|            |                           |                 | `(bvult (bvadd y x) 1)`       | user	0m0.048s  | Timeout                 | user	0m0.033s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.043s  | Timeout                 | sys	0m0.042s |                                              |
| andex      | `x = 1 \|= x & y == 1`    | `x = 1 ^ y = 1` | `(= 1 y)`                     | real	0m1.161s  | `(= 1 y)`               | real	3m0.002s |                                              |
|            |                           |                 | `(bvult (bvsrem 1 y) 1)`      | user	0m0.866s  | `(bvult (bvxor 1 y) y)` | user	0m0.037s |                                              |
|            |                           |                 | `(= (bvmul y y) 1)`           | sys	0m0.168s  | Timeout                 | sys	0m0.041s |                                              |
| file       | `x < 100 \|= x + 1 < 100` | `x < 99`        | `(bvult x 1)`                 | real	0m0.419s  | `(bvult x 1)`           | real	0m0.447s |                                              |
|            |                           |                 | `(bvult 100 x)`               | user	0m0.271s  | `(bvult 100 x)`         | user	0m0.279s |                                              |
|            |                           |                 | `(= 1 x)`                     | sys	0m0.133s  | `(= 1 x)`               | sys	0m0.112s |                                              |
| maxint     | `\|= x + 1 > x`           | `x < maxint`    | `(bvult x 1)`                 | real	3m0.004s  | `(bvult x 1)`           | real	3m0.002s |                                              |
|            |                           |                 | `(bvult x 255)`               | user	0m0.039s  | `(bvult x 4294967295)`  | user	0m0.045s |                                              |
|            |                           |                 | Timeout                       | sys	0m0.046s  | Timeout                 | sys	0m0.029s |                                              |
| multident  | `\|= x * y == x`          | `y = 1`         | `(bvult x 1)`                 | real	0m5.814s  | `(x = 0)`               | real	3m0.002s |                                              |
|            |                           |                 | `(= 1 y)`                     | user	0m5.556s  | `(x = 1)`               | user	0m0.038s |                                              |
|            |                           |                 | `(= (bvmul y x) x)`           | sys	0m0.155s  | Timeout                 | sys	0m0.048s |                                              |
| multinv    | `\|= x * y == x`          | `y = 0`         | `(= x 0)`                     | real	0m1.029s  | `(x = 0)`               | real	3m0.002s |                                              |
|            |                           |                 | `(= y 0)`                     | user	0m0.887s  | `(x = 1)`               | user	0m0.059s |                                              |
|            |                           |                 | `(= (bvmul y x) 0)`           | sys	0m0.106s  | Timeout                 | sys	0m0.027s |                                              |
| trans      | `x > y \|= x > z`         | `y > z`         | `(= z y)`                     | real	0m3.052s  | `(= z y)`               | real	3m0.002s |                                              |
|            |                           |                 | `(= (bvsdiv y z) z)`          | user	0m2.851s  | Timeout                 | user	0m0.036s |                                              |
|            |                           |                 | `(= (bvurem y x) z)`          | sys	0m0.138s  | Timeout                 | sys	0m0.041s |                                              |

### File Structure
- The C files for the 8-bit integer version of these examples are in `cFiles8bit/` and those for the 32-bit integer version are in `cFiles32bit/`.
- `smtFiles8bitCvc5/` and `smtFiles32bitCvc5/` contain the SMT files generated by crux using cvc5 with abduction queries made in the sat case.
- `smtFiles8bitCvc5Rwr/` contains hand-written SMT files representing the baseline - this is what I imagine the queries corresponding to the example C files would like like. 