#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main() {
  /////////////
  // doubles //
  /////////////
  double dx = crucible_double("dx");

  double d01 = exp(dx);
  double d02 = exp2(dx);
  double d03 = log(dx);
  double d04 = log2(dx);
  double d05 = log10(dx);
  double d06 = sin(dx);
  double d07 = cos(dx);

  // sqrt unit tests
  check(sqrt(+0) == +0);
  check(sqrt(-0) == -0);
  check(sqrt(INFINITY) == INFINITY);
  check(isnan(sqrt(NAN)));
  check(isnan(sqrt(-1)));

  ////////////
  // floats //
  ////////////
  float fx = crucible_double("fx");

  float f01 = expf(fx);
  float f02 = exp2f(fx);
  float f03 = logf(fx);
  float f04 = log2f(fx);
  float f05 = log10f(fx);
  float f06 = sinf(fx);
  float f07 = cosf(fx);

  // sqrt unit tests
  check(sqrtf(+0) == +0);
  check(sqrtf(-0) == -0);
  check(sqrtf(INFINITY) == INFINITY);
  check(isnan(sqrtf(NAN)));
  check(isnan(sqrtf(-1)));

  return 0;
}
