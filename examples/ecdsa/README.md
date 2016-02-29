This directory contains two implementations of the Elliptic Curve
Digital Signature Algorithm (ECDSA) over the NIST P384 curve, along with
a SAWScript program that proves them equivalent. The
[first](cryptol-spec), in Cryptol, is intended to closely resemble the
English specification of the algorithm. The
[second](src/com/galois/ecc), in Java, is efficiently executable and
performs no allocation during the signature generation or verification
process.

# Running the Proof

The script `ecdsa.saw` in this directory performs a proof of
equivalence between the Java ECDSA implementation contained in
`ecdsa.jar` and the Cryptol specification in `cryptol-spec`.

The included `Makefile` attempts to locate the JDK by running the `java`
command and interpreting some of its debugging output. This is not
always effective, however, so you may have to set the `JDK` environment
variable to point to the correct location of `rt.jar` (or `classes.jar`,
for some old JVM distributions). It also assumes that `saw` is located
in the `bin` directory in the top level of the `saw-script` working
directory. To have it use a different executable, set the `SAW`
environment variable.

The top-level target in the `Makefile` just builds the Java source. To
run the verification, as well, use:

~~~~
make verify
~~~~
