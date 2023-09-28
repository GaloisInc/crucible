#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main(void) {
  ////////////
  // double //
  ////////////
  double d1 = 42.5;     // Normal
  double d2 = INFINITY; // Not normal
  double d3 = NAN;      // Not normal

  check(isnormal(d1));
  check(!(isnormal(d2)));
  check(!(isnormal(d3)));

  check(__builtin_isnormal(d1));
  check(!(__builtin_isnormal(d2)));
  check(!(__builtin_isnormal(d3)));

  ///////////
  // float //
  ///////////
  double f1 = 42.5f;    // Normal
  double f2 = INFINITY; // Not normal
  double f3 = NAN;      // Not normal

  check(isnormal(f1));
  check(!(isnormal(f2)));
  check(!(isnormal(f3)));

  check(__builtin_isnormal(f1));
  check(!(__builtin_isnormal(f2)));
  check(!(__builtin_isnormal(f3)));

  return 0;
}
