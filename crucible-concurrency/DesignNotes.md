# crucible-concurrency: concurrency-enabled symbolic simulation

This package exposes a library for enabling the symbolic simulation of
multithreaded programs via Crucible. This document should help (1) add
concurrency support to a language that already has a Crucible translation/Crux
frontend, and (2) help explain the design of crucible-concurrency for developers.

## Overview

Crucible-concurrency (or simply Crucibles[^1]) is a package that uses Crucible to
perform symbolic simulation of multithreaded programs. At the highest level of
abstraction, it achieves this by repeatedly executing a Crucible program, each
time exploring a different thread interleaving.

The library uses Crucible to perform multithreaded symbolic simulation by
recognizing certain _hooks_ in the Crucible code to be explored. These _hooks_
can be thought of as functions denoting that a global access is about to occur,
that a thread is about to be spawned, that a lock is going to be acquired, etc.

When Crucibles encounters one of these hooks, it decides whether or not the
current thread should be preempted by consulting a scheduling algorithm. When
execution terminates, the same scheduling algorithm decides if it should try to
find a new thread interleaving to explore, or if should terminate.

## Using crucible-concurrency in a new language

The main thing a client language needs to provide in order to get support from
Crucibles is to implement a set of primitive matchers. These matchers inspect a
Crucible Call statement, and can return a Crucibles-defined primitive value. The
primitives that Crucibles understands are enumerated by the `ExplorePrimitive`
type in `Crucibles.Primitives`.

An example implementation for `crucible-syntax` is defined by
`crucibleSyntaxPrimitives` in the same module.

## Modifying crucible-concurrency

Crucibles is driven by an `ExecutionFeature`, `scheduleFeature`, defined in
`Crucibles.Explore`. The idea is that this feature should not be making many
decisions about which thread to run next: its main task is to maintain the state
of the currently running threads, including knowing how to suspend and resume
them, how to check to see if they are enabled, etc.

Scheduling decisions are factored out into a `SchedulingAlgorithm` typeclass in
`Crucibles.SchedulingAlgorithm`. The design of this class is somewhat ad-hoc as
this package is quite experimental. The interface permits the execution feature
to communicate to the algorithm that important scheduling events have occurred,
and to query the algorithm for threads to run, given a list of enabled threads.

### Execution Graphs

The main data structure that both the execution feature and the scheduling
algorithm understand, then, is an execution graph (in practice a tree, but
perhaps in the future there may be a reason plus a clever way to make this a
graph), `Executions`, defined in `Crucibles.Executions`.

A single execution in `Crucibles` is a sequence of events: an event is an access
(read or write of some resource), a thread spawn, a thread exit, etc. Each event
has a unique predecessor (except for the first event), but each event may have
several successors, corresponding to executing one of a number of enabled
threads, taking a branch one way or the other, etc. Thus, exploring a single
execution results in adding a new sequence of events to `Executions`.

As executions are explored, they are added to `Executions`, resulting in a graph
of event sequences.

### DPOR Scheduling Algorithm:

An implementation of SchedulingAlgorithm is provided in the `Crucibles.DPOR`
module, based on the algorithm described by Flanagan and Godefroid (2005). While
their paper provides a more complete explanation, central to the algorithm is
identifying backtracking points: events where the action of thread `p` was
explored where we should try and explore thread `q`. Doing so requires being
able to identify events that conflict with each other: the event graph is
exactly the structure used for this purpose.


## Implementation Notes and Curiosities

The following is a list of TODOs, implementation warts, and other oddities.

### Progress and Fairness

Due to the use of DPOR, if there are state space cycles then eventually the
exploration will get stuck in such a cycle. For example, in program where two
threads `thread1` and `thread2` are executing, as in (the equivalent of):

```
int p;

void thread1() {
  while(true) {
    m.lock();
    cond = p == 1;
    m.unlock();
    if (cond) {
      break;
    }
  }
}

void thread2() {
  m.lock();
  p = 1;
  m.unlock();
}
```

There is an execution in which `thread1` is never preempted, and hence never
exits -- and the program never terminates. While there are techniques to deal
with this in a variety of ways, none are implemented. A _workaround_ when using
a configuration that might get stuck in such a loop, is to add a counter that
tracks the number of iterations through the loop, and to add an `assume`
statement that bounds the value of this variable. While this is of course an
unsound abstraction of the original program, it does ensure termination.

### Resource Naming

One key challenge in adding Crucibles support is figuring out a scheme for
naming each resource. That is, two mutexes may have source names `m1` and
`m2`, but we need a global identifier: usually this is amounts to an address
of some sort. 

The next point to understand is that when Crucibles is exploring a path, it
only add events to the event graph if they haven't been seen. For example, if
we discover an execution by running thread `p`, then `q`, `r` (`p.q.r`), and
then restart and discover `p.q.p`, we will end up with an event graph like:

```
e0 -> e1 -> e2
       `-> e3
```

Now suppose each event corresponds to a write of variable `x`. On the first
run, the event graph will really look like:

```
e0(&addr) -> e1(&addr) -> e2(&addr)
```

On the subsequent execution, `p` touches the same resource but it may have a
different address. We have a choice here: when we explore the same thread as a
previous execution, we could _merge_ the set of resources, resulting in:

```
e0({&addr, &addr'}) -> e1{&addr, &addr'} -> e2{&addr, &addr'}
                        `-> e3{&addr, &addr'}
```

But this would quickly grow without bound. 

Therefore the current assumption is that, along some control flow path (both
branches and threads taken), the resources accessed are the same but for a
substitution of names. Thus, we will _rename_ resources as we encounter
already-explored events.

*N.B.* This should be opaque to scheduling algorithms *WITH THE ASSUMPTION* that
they only ever inspect the _current_ event trace. If we need to break this
assumption, then we will need to ensure that names are stable across executions:
the exact method will be language dependent, and may require adding additional
primitives that Crucibles can understand. One question is to what extent names
need to be stable across different control flow paths.

### Branches

Because merging scheduler state is not well defined, we perform no path merging:
instead, we try to explore both branches of a `SymbolicBranchState`. We may want
to investigate a way of determining which branches do not result in changes to
the scheduler state, and allow them to be merged. This may require a
pre-analysis.

### Misc. Questions

- We do not store any symbolic state, and instead execute the entire program
  from start to finish for each execution. Does this make sense?
  
- Somewhat related: could this have been implemented more like the DFS
  exploration execution feature?

- Adding support for relaxed memory models is a rather large open question:
  should this go in `Crucibles`, or can/should that be modeled by the client
  language in a way that appears opaque to `Crucibles`?

- The system is set up to be able to yield on multiple resources. However, 
  we probably need to make these types intrinsics so that we can inspect the mux tree.

[^1]: That is, the plural of `crucible`.
