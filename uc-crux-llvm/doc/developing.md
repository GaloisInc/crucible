# Developers' Documentation

## Tooling

### `hlint`

UC-Crux should have no warnings from `hlint`. Run it like so:
```bash
hlint src test
```
If any of its suggestions are unhelpful, add ignore rules to `.hlint.yaml`.

## Related Work

To understand the challenges addressed by UC-Crux and to provide inspiration for
further work, refer to the following literature.

### Under-Constrained Symbolic Execution: Correctness Checking for Real Code

[Link](https://www.usenix.org/conference/usenixsecurity15/technical-sessions/presentation/ramos).
This paper introduces the idea of local symbolic execution. The primary
difference between the technique described here and UC-Crux is that UC-Crux has
an unmodified memory model, and so executes each function multiple times to
infer a memory layout sufficient for its successful execution.

### HotFuzz: Discovering Algorithmic Denial-of-Service Vulnerabilities Through Guided Micro-Fuzzing

[Link](https://arxiv.org/abs/2002.03416). This paper describes a system for
testing Java programs that uses a technique called "micro fuzzing". The authors
state:

> Micro-fuzzing represents a drastically different approach to vulnerability
> detection than traditional automated wholeprogram fuzzing. In the latter case,
> inputs are generated for an entire program either randomly, through mutation of
> seed inputs, or incorporating feedback from introspection on execution.
> Whole-program fuzzing has the significant benefit that any abnormal
> behavior—i.e., crashes—that is observed should be considered as a real bug as by
> definition all the constraints on the execution path that terminates in the bug
> are satisfied (up to the determinism of the execution). However, whole-program
> fuzzing also has the well-known drawback that full coverage of the test artifact
> is difficult to achieve. Thus, an important measure of a traditional fuzzer’s
> efficacy is its ability to efficiently cover paths in a test artifact.
>
> Micro-fuzzing strikes a different trade-off between coverage and path
> satisfiability. Inspired by the concept of microexecution [24], micro-fuzzing
> constructs realistic intermediate program states, defined as Java objects, and
> directly executes individual methods on these states. Thus, we can cover all
> methods by simply enumerating all the methods that comprise a test artifact,
> while the difficulty lies instead in ensuring that constructed states used as
> method inputs are feasible in practice.

Replace "fuzzing" with "symbolic execution", and virtually all of this applies
word-for-word to UC-Crux.

### JCrasher

[Link](http://cgi.di.uoa.gr/~smaragd/jcrasher.pdf). This testing tool for Java
also invents (random) arguments for each function and uses heuristics to
classify the resulting exceptions.
