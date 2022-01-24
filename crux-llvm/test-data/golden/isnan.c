#include <crucible.h>
#include <math.h>

int main() {
  // double
  double d = NAN;
  check(isnan(d));
  check((isnan)(d)); // The parentheses around (isnan) are important here,
                          // as this instructs Clang to compile isnan as a
                          // direct function call rather than as a macro.
  check(__isnan(d));
  check(__builtin_isnan(d));

  // float
  float f = NAN;
  check(isnan(f));
  check((isnan)(f));
  check(__isnanf(f));
  check(__builtin_isnan(f));

  return 0;
}
