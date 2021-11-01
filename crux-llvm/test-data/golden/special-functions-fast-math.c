#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main() {
  /////////////
  // doubles //
  /////////////
  double dx = crucible_double("dx");
  double dy = crucible_double("dy");

  double d01 = exp(dx);
  double d02 = exp2(dx);
  double d03 = log(dx);
  double d04 = log2(dx);
  double d05 = log10(dx);
  double d06 = sin(dx);
  double d07 = cos(dx);
  double d08 = pow(dx, dy);

  // ceil unit tests
  check(ceil(-0.4) == 0);
  check(ceil(-0.5) == 0);
  check(ceil(-0.6) == 0);
  check(ceil(0.4) == 1);
  check(ceil(0.5) == 1);
  check(ceil(0.6) == 1);
  check(ceil(+0) == +0);
  check(ceil(-0) == -0);
  check(ceil(+INFINITY) == +INFINITY);
  check(ceil(-INFINITY) == -INFINITY);
  check(isnan(ceil(NAN)));

  // floor unit tests
  check(floor(-0.4) == -1);
  check(floor(-0.5) == -1);
  check(floor(-0.6) == -1);
  check(floor(0.4) == 0);
  check(floor(0.5) == 0);
  check(floor(0.6) == 0);
  check(floor(+0) == +0);
  check(floor(-0) == -0);
  check(floor(+INFINITY) == +INFINITY);
  check(floor(-INFINITY) == -INFINITY);
  check(isnan(floor(NAN)));

  // sqrt unit tests
  check(sqrt(+0) == +0);
  check(sqrt(-0) == -0);
  check(sqrt(INFINITY) == INFINITY);
  check(isnan(sqrt(NAN)));
  check(isnan(sqrt(-1)));

  ////////////
  // floats //
  ////////////
  float fx = crucible_float("fx");
  float fy = crucible_float("fy");

  float f01 = expf(fx);
  float f02 = exp2f(fx);
  float f03 = logf(fx);
  float f04 = log2f(fx);
  float f05 = log10f(fx);
  float f06 = sinf(fx);
  float f07 = cosf(fx);
  float f08 = powf(dx, dy);

  // ceilf unit tests
  check(ceilf(-0.4) == 0);
  check(ceilf(-0.5) == 0);
  check(ceilf(-0.6) == 0);
  check(ceilf(0.4) == 1);
  check(ceilf(0.5) == 1);
  check(ceilf(0.6) == 1);
  check(ceilf(+0) == +0);
  check(ceilf(-0) == -0);
  check(ceilf(+INFINITY) == +INFINITY);
  check(ceilf(-INFINITY) == -INFINITY);
  check(isnan(ceilf(NAN)));

  // floorf unit tests
  check(floorf(-0.4) == -1);
  check(floorf(-0.5) == -1);
  check(floorf(-0.6) == -1);
  check(floorf(0.4) == 0);
  check(floorf(0.5) == 0);
  check(floorf(0.6) == 0);
  check(floorf(+0) == +0);
  check(floorf(-0) == -0);
  check(floorf(+INFINITY) == +INFINITY);
  check(floorf(-INFINITY) == -INFINITY);
  check(isnan(floorf(NAN)));

  // sqrtf unit tests
  check(sqrtf(+0) == +0);
  check(sqrtf(-0) == -0);
  check(sqrtf(INFINITY) == INFINITY);
  check(isnan(sqrtf(NAN)));
  check(isnan(sqrtf(-1)));

  return 0;
}
