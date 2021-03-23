This package is for experimenting with adding model-checking
support to Crucible.

Running
-------

First, compile the C files to bitcode files:

```
(cd test && make)
```

Then you can run `crucible-mc` like so:

```
crucible-mc test/loop-simple-deep-nested.bc main
```

where the first argument is a bitcode file, and the second argument is a
function symbol within that file.
