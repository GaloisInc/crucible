// Ensure that Crux's CVC5 solver backend uses IEEE-754 floating-point
// semantics by default. The `check` below will yield a counterexample with
// IEEE-754, as NaN is not equal to itself.
#include <crucible.h>

int main(void) {
    double d = crucible_double("d");
    check(d == d);
    return 0;
}
