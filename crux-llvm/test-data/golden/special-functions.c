#define _GNU_SOURCE
#include <crucible.h>
#include <math.h>

int main() {
  ///////////////
  // constants //
  ///////////////
  double c01 = M_PI;
  double c02 = M_PI_2;
  double c03 = M_PI_4;
  double c04 = M_1_PI;
  double c05 = M_2_PI;
  double c06 = M_2_SQRTPI;
  double c07 = M_SQRT2;
  double c08 = M_E;
  double c09 = M_LOG2E;
  double c10 = M_LOG10E;
  double c11 = M_LN2;
  double c12 = M_LN10;

  /////////////
  // doubles //
  /////////////
  double dx = crucible_double("dx");
  double dy = crucible_double("dy");

  double d01 = exp(dx);
  double d02 = expm1(dx);
  double d03 = exp2(dx);
  double d04 = exp10(dx);
  double d05 = log(dx);
  double d06 = log1p(dx);
  double d07 = log2(dx);
  double d08 = log10(dx);
  double d09 = sin(dx);
  double d10 = tan(dx);
  double d11 = cos(dx);
  double d12 = asin(dx);
  double d13 = atan(dx);
  double d14 = acos(dx);
  double d15 = sinh(dx);
  double d16 = tanh(dx);
  double d17 = cosh(dx);
  double d18 = asinh(dx);
  double d19 = atanh(dx);
  double d20 = acosh(dx);
  double d21 = hypot(dx, dy);
  double d22 = atan2(dx, dy);

  // sqrt unit tests
  check(sqrt(+0) == +0);
  check(sqrt(-0) == -0);
  check(sqrt(INFINITY) == INFINITY);
  check(isnan(sqrt(NAN)));

  ////////////
  // floats //
  ////////////
  float fx = crucible_double("fx");
  float fy = crucible_double("fy");

  float f01 = expf(fx);
  float f02 = expm1f(fx);
  float f03 = exp2f(fx);
  float f04 = exp10f(fx);
  float f05 = logf(fx);
  float f06 = log1pf(fx);
  float f07 = log2f(fx);
  float f08 = log10f(fx);
  float f09 = sinf(fx);
  float f10 = tanf(fx);
  float f11 = cosf(fx);
  float f12 = asinf(fx);
  float f13 = atanf(fx);
  float f14 = acosf(fx);
  float f15 = sinhf(fx);
  float f16 = tanhf(fx);
  float f17 = coshf(fx);
  float f18 = asinhf(fx);
  float f19 = atanhf(fx);
  float f20 = acoshf(fx);
  float f21 = hypotf(fx, fy);
  float f22 = atan2f(fx, fy);

  // sqrt unit tests
  check(sqrtf(+0) == +0);
  check(sqrtf(-0) == -0);
  check(sqrtf(INFINITY) == INFINITY);
  check(isnan(sqrtf(NAN)));

  return 0;
}
