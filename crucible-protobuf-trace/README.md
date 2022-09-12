This package implements a Protobuf trace of the events performed by Crucible during symbolic simulation. This can be
used to test things like other memory models outside of the runningn crucible system, allowing us to easily test
implementations from other projects as well as ones implemented in other languages, e.g. quick prototypes in Python.

This trace is currently planned to consist of 2 components:
1. The main event trace encas protobuf
2. symbolic expressions serialized as SExpressions as provided by what4-serialize

The symbolic are currently encoded via what4-serialize to get something working set up quickly, however encoding them as
protobuf messages as well is an option to be considered in the future if the interoperability becomes an issue.
