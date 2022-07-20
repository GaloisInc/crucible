#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main(void) {
  ////////////
  // double //
  ////////////
  double d1 = 42.5;      // Finite
  double d2 = INFINITY;  // Infinite
  double d3 = -INFINITY; // Infinite
  double d4 = NAN;       // Not infinite (and also not finite)

  check(isinf(d1) ==  0);
  check(isinf(d2) ==  1);
  check(isinf(d3) == -1);
  check(isinf(d4) ==  0);

#if !defined(__APPLE__)
  // The parentheses around (isinf) are important here, as this instructs Clang
  // to compile isinf as a direct function call rather than as a macro. This is
  // not portable, however, For instance, macOS only provides isinf as a macro,
  // not as a function.
  check((isinf)(d1) ==  0);
  check((isinf)(d2) ==  1);
  check((isinf)(d3) == -1);
  check((isinf)(d4) ==  0);

  check(__isinf(d1) ==  0);
  check(__isinf(d2) ==  1);
  check(__isinf(d3) == -1);
  check(__isinf(d4) ==  0);
#endif

  check(__builtin_isinf_sign(d1) ==  0);
  check(__builtin_isinf_sign(d2) ==  1);
  check(__builtin_isinf_sign(d3) == -1);
  check(__builtin_isinf_sign(d4) ==  0);

  ///////////
  // float //
  ///////////
  float f1 = 42.5f;     // Finite
  float f2 = INFINITY;  // Infinite
  float f3 = -INFINITY; // Infinite
  float f4 = NAN;       // Not infinite (and also not finite)

  check(isinf(f1) ==  0);
  check(isinf(f2) ==  1);
  check(isinf(f3) == -1);
  check(isinf(f4) ==  0);

#if !defined(__APPLE__)
  check((isinf)(f1) ==  0);
  check((isinf)(f2) ==  1);
  check((isinf)(f3) == -1);
  check((isinf)(f4) ==  0);

  check(__isinff(f1) ==  0);
  check(__isinff(f2) ==  1);
  check(__isinff(f3) == -1);
  check(__isinff(f4) ==  0);
#endif

  check(__builtin_isinf_sign(f1) ==  0);
  check(__builtin_isinf_sign(f2) ==  1);
  check(__builtin_isinf_sign(f3) == -1);
  check(__builtin_isinf_sign(f4) ==  0);

  return 0;
}
