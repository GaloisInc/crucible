#include <assert.h>

extern float __VERIFIER_nondet_float(void);
void __VERIFIER_assume(int cond) {
  if (!cond) {
    abort();
  }
}
void __VERIFIER_assert(int cond) {
  assert(cond);
}

int main()
{
    float a = __VERIFIER_nondet_float();
    float b = __VERIFIER_nondet_float();
    __VERIFIER_assume(a >= 1.e30f);
    __VERIFIER_assume(b <= 1.f);
    __VERIFIER_assume(b >= 0.f);
    float r = a + b;
    __VERIFIER_assert(a == r);

    return 0;
}
