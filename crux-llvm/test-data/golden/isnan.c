#include <crucible.h>
#include <math.h>

int main() {
  // double
  double d = NAN;
  check(isnan(d));
#if !defined(__APPLE__)
  // The parentheses around (isnan) are important here, as this instructs Clang
  // to compile isnan as a direct function call rather than as a macro. This is
  // not portable, however, For instance, macOS only provides isnan as a macro,
  // not as a function.
  check((isnan)(d));
  check(__isnan(d));
#endif
  check(__builtin_isnan(d));

  // float
  float f = NAN;
  check(isnan(f));
#if !defined(__APPLE__)
  check((isnan)(f));
  check(__isnanf(f));
#endif
  check(__builtin_isnan(f));

  return 0;
}
