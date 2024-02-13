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

  // The C standard only requires that isinf(x) return a non-zero value when x
  // is infinite. Unlike __builtin_isinf_sign(x), we cannot guarantee that this
  // return value will be a specific number, so we make the tests below as
  // generic as possible.
  check(!(isinf(d1)));
  check(isinf(d2));
  check(isinf(d3));
  check(!(isinf(d4)));

#if !defined(__APPLE__)
  // The parentheses around (isinf) are important here, as this instructs Clang
  // to compile isinf as a direct function call rather than as a macro. This is
  // not portable, however, For instance, macOS only provides isinf as a macro,
  // not as a function.
  check(!((isinf)(d1)));
  check((isinf)(d2));
  check((isinf)(d3));
  check(!((isinf)(d4)));

  check(!(__isinf(d1)));
  check(__isinf(d2));
  check(__isinf(d3));
  check(!(__isinf(d4)));
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

  check(!(isinf(f1)));
  check(isinf(f2));
  check(isinf(f3));
  check(!(isinf(f4)));

#if !defined(__APPLE__)
  check(!((isinf)(f1)));
  check((isinf)(f2));
  check((isinf)(f3));
  check(!((isinf)(f4)));

  check(!(__isinff(f1)));
  check(__isinff(f2));
  check(__isinff(f3));
  check(!(__isinff(f4)));
#endif

  check(__builtin_isinf_sign(f1) ==  0);
  check(__builtin_isinf_sign(f2) ==  1);
  check(__builtin_isinf_sign(f3) == -1);
  check(__builtin_isinf_sign(f4) ==  0);

  return 0;
}
