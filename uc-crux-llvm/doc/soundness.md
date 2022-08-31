# Soundness

A program analysis is *sound* if every claim it makes is true. UC-Crux has
applications as both a bug-finding tool and a verification[^1] tool, and these
use-cases have different soundness criteria: a bug-finding tool is sound if
whenever it claims that there is a bug in the program that bug is actually
possible in some execution of the program; a verification tool is sound if
whenever it claims that a program is safe every possible execution of the
program is safe.

Given these complementary properties, there are four possible criteria for
soundness that each analysis feature of UC-Crux might meet:

- Overapproximate: The feature reflects a superset of the set of possible
  program behaviors
- Underapproximate: The feature reflects a subset of the set of possible program
  behaviors
- Precise: Both over- and under-approximate, that is, the feature exactly
  reflects the actual set of possible program behaviors
- Indefinite: Neither over-approximate nor under-approximate, that is, the
  feature doesn't necessarily bear any of the above relationships to the set of
  possible program behaviors; such features might also be called *unsound* to
  denote that they don't meet a specific soundness criterion

The following table shows how these labels correspond to soundness for both
verification and bug-finding:

| Property         | Sound for verification | Sound for bugfinding |
|:-----------------|:----------------------:|:--------------------:|
| Overapproximate  | Y                      | N                    |
| Underapproximate | N                      | Y                    |
| Precise          | Y                      | Y                    |
| Indefinite       | N                      | N                    |

These degrees of soundness form a partial order by inclusion with the following
Hasse diagram, which means that every precise feature is also over- and
under-approximate, and any over- or under-approximate feature can also be
considered indefinite.

```
       Indefinite
      /         \
Overapprox    Underapprox
      \         /
        Precise
```

This Venn diagram shows some realizable overlaps between these concepts:

<!-- Source: https://docs.google.com/drawings/d/1SGTh6XXOf-pT28x8a7dJLXPcQUBq6YkjZXkU0Nw_KPs -->

![Venn diagram](./soundness.svg)

[The documentation on specifying functions](doc/specs.md) describes how these
criteria apply to that particular feature; reviewing that documentation may be
helpful in understanding them.

## Generic Sources of Unsoundness

There are several sources of unsoundness in UC-Crux that aren't by design, and
can't always be avoided.

- As with any piece of software that is not formally verified, UC-Crux itself
  surely has bugs (and relies on the correctness of a complex stack of software
  and hardware including SMT solvers, operating systems, CPUs, etc. that
  themselves all have bugs). Any claims it makes are conditional upon not
  encountering such bugs.
- C, C++, Rust, and LLVM all lack official formalized semantics, so
  Crucible-LLVM (and so UC-Crux) contains a best-effort approximation based on
  the C standard and the LLVM language reference.
- There are certain kinds of behaviors that are undefined at the C or C++ level
  that aren't visible at the LLVM level, such as signed overflow and ill-typed
  reads out of unions. UC-Crux can’t detect these, since it operates on LLVM
  code. Crucible-LLVM has limited support for symbolically executing programs
  compiled with UndefinedBehaviorSanitizer, which partially addresses these
  issues.
- UC-Crux will not (yet!) generate aliasing pointers, nor cyclic data
  structures. Undefined behaviors that occur only in such circumstances will be
  undetected.
- All of the [limitations that apply to
  Crux-LLVM](../../crucible-llvm/doc/limitations.md)
  ([permalink][crux-llvm-limitations]) apply to UC-Crux as well.

## Unsound Features

UC-Crux has a few intentionally unsound features that may still be useful for
bug-finding or verification.

### Skipping External Functions

When encountering a call to an external function, UC-Crux can *skip* the
execution of that function. For instance, in the following program:

```c
extern void log(const char *msg);
unsigned int my_add(unsigned int x, unsigned int y) {
  log("Adding two unsigned integers...");
  return x + y;
}
```

UC-Crux will skip the call to `log` by default, and report that the function
`my_add` is safe. This seems reasonable in this example, but in general this
feature is *indefinite* AKA *unsound* in the sense described above.

<!-- TODO(lb): Would be nice to have examples of where this is not
over-approximate and where it is not under-approximate. -->

### Specifications

See [the documentation on specifying functions](doc/specs.md). Specifications
may individually meet any of the soundness criteria.

### Unsound Library Functions

UC-Crux has built-in unsound (indefinite) versions of the following library
functions:

- `getenv`
- `gethostname`

## Toggling Unsound Features

You can limit the kinds of unsound features that UC-Crux employs using the
`--soundness` CLI flag. By default, it has the value `indefinite`, but may also
be set to `overapprox`, `underapprox`, or `precise`. In these more stringent
modes, UC-Crux will disable features that don't meet the given soundness
criterion.

[^1]: Verification in the sense of verifying the absence of undefined behavior.

[crux-llvm-limitations]: https://github.com/GaloisInc/crucible/blob/555acf77477a02c8b0e101c2c5fcdb9a88338382/crucible-llvm/doc/limitations.md
