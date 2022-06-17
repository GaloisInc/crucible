# Specifying Functions

Users can provide specifications of functions to UC-Crux (represented as JSON).
This can be used to provide sound and precise descriptions of external or
library functions, to speed up symbolic execution by specifying defined (but
costly) functions, or even to expand the coverage of UC-Crux by approximately
specifying functions that would trigger symbolic execution timeouts or
loop/recursion bounds.

## Motivation

Consider the following program:
```c
extern int *f(void);
extern int g(void);

int main() {
  int *x = f();
  *x = 5;
  return g();
}
```
By default, UC-Crux can't tell if this function is safe or has a bug - it
depends on whether `f` returns a valid pointer.
```
$ uc-crux-llvm --entry-points main test.c
[UC-Crux-LLVM] Results for main
[UC-Crux-LLVM] Unclear result, errors are either false or true positives (or timeouts were hit):
[UC-Crux-LLVM] Unclassified error:
[UC-Crux-LLVM] The region wasn't allocated, wasn't large enough, or was marked as readonly
[UC-Crux-LLVM] at test.c:6:6
[UC-Crux-LLVM] in context:
[UC-Crux-LLVM]   main
[UC-Crux-LLVM]  at test.c:6:6
```
However, if the user provides a specification for `f` that says that it always
returns a valid pointer to space for one 32-bit integer, then UC-Crux can tell
that `main` is safe (modulo the behavior of `g`):
```json
{
    "f": [{
        "Pre": { "ArgPreconds": [] },
        "PreSound": "Precise",
        "Post": {
            "ArgClobbers": [],
            "GlobalClobbers": {},
            "ReturnValue": {
                "Type": {
                    "tag": "Ptr",
                    "contents": {
                        "tag": "Full",
                        "contents": { "tag": "Int", "contents": 32 }
                    }
                },
                "Value": {
                    "tag": "Ptr",
                    "contents": [ [], { "tag": "Allocated", "contents": 1 } ]
                }
            }
        },
        "PostSound": "Precise"
    }]
}
```
```
$ uc-crux-llvm --specs-path specs.json --entry-points main test.c

[UC-Crux-LLVM] Results for main
[UC-Crux-LLVM] Function is always safe.
[UC-Crux-LLVM] In addition to any assumptions listed above, the following sources of unsoundness may invalidate this safety claim:
[UC-Crux-LLVM]   Execution of the following functions was skipped:
[UC-Crux-LLVM]   - g
```

## Soundness of Specifications

Specifications don't have to exactly describe the behavior of a function in
order to be useful. For instance, for the purposes of verification it's
acceptable to use a specification with a stronger precondition than the actual
implementation. If verification succeeds against this stronger spec, then the
program also must respect the weaker contract of the implementation. Dually,
when hunting for bugs one might use a specification with a weaker
postcondition - e.g., if a function *may* return a null pointer under some
precondition, one could use a spec with a postcondition stating that the
function *always* returns a null pointer when that precondition is met.

Clearly, the requirements on specifications depend on the use-case. Accordingly,
the pre- and post-conditions of specs are accompanied by *soundness tags* which
indicate whether they over-approximate function behaviors, under-approximate
them, both, or neither. There are four possible tags, the meaning of which
depends on whether they are applied to preconditions or postconditions.

- `Overapprox`: For preconditions, means that the specified preconditions are
  more restrictive than the actual implementation. For postconditions, it means
  that the specified postcondition encapsulates all possible effects of the
  implementation on the program state under the accompanying precondition.
- `Underapprox`: For preconditions, means that the specified preconditions are
  less restrictive than the actual implementation. For postconditions, means
  that the specified postcondition encapsulates some definitely possible effects
  of the implementation on the program state under the accompanying precondition.
- Precise: Both over-approximate nor under-approximate.
- Imprecise: Neither over-approximate nor under-approximate.

These tags form a partial order with the following Hasse diagram:

```
       Imprecise
      /         \
Overapprox    Underapprox
      \         /
        Precise
```

The ordering means: Anything that is `Precise` can also be counted as either
`Overapprox` or `Underapprox`, and if you're willing to accept `Imprecise`,
then you would be willing to accept any degree of precision as well.

UC-Crux doesn't yet use the soundness tags internally, but the intention is that
they will be tracked and reported along with the analysis results, and that
users would be able to indicate that they're only interested in results using
over- or under-approximate specs.

## JSON Format

The JSON format for writing specifications is not yet stable. In the meantime,
`src/UCCrux/LLVM/Spec` and `src/UCCrux/LLVM/Views/Spec` provide some indication
of how it works.
