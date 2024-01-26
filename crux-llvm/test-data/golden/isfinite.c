#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main(void) {
  ////////////
  // double //
  ////////////
  double d1 = 42.5;     // Finite
  double d2 = INFINITY; // Infinite
  double d3 = NAN;      // Not infinite (and also not finite)

  check(isfinite(d1));
  check(!(isfinite(d2)));
  check(!(isfinite(d3)));

  check(__builtin_isfinite(d1));
  check(!(__builtin_isfinite(d2)));
  check(!(__builtin_isfinite(d3)));

  ///////////
  // float //
  ///////////
  float f1 = 42.5f;    // Finite
  float f2 = INFINITY; // Infinite
  float f3 = NAN;      // Not infinite (and also not finite)

  check(isfinite(f1));
  check(!(isfinite(f2)));
  check(!(isfinite(f3)));

  check(__builtin_isfinite(f1));
  check(!(__builtin_isfinite(f2)));
  check(!(__builtin_isfinite(f3)));

  return 0;
}
