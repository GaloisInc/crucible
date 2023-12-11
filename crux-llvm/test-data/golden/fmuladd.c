// A regression test for https://github.com/GaloisInc/crucible/issues/1154.
#include <crucible.h>
#include <math.h>

// LLVM is liable to optimize these functions in a way that uses the
// llvm.fmuladd.* or llvm.fma.* intrinsics.
float fmuladdf(float a, float b, float c) {
  return a * b + c;
}

double fmuladd(double a, double b, double c) {
  return a * b + c;
}

int main(void) {
  float f1 = fmuladdf(1.0f, 2.0f, 3.0f);
  check(f1 == f1);
  float f2 = fmaf(1.0f, 2.0f, 3.0f);
  check(f2 == f2);

  double d1 = fmuladd(1.0, 2.0, 3.0);
  check(d1 == d1);
  double d2 = fma(1.0, 2.0, 3.0);
  check(d2 == d2);

  return 0;
}
