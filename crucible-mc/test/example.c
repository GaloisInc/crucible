#include <stdbool.h>
#include <stdint.h>

volatile int iGlob = 0;
volatile bool bGlob = false;

void __VERIFIER_assert(uint32_t v);
void __VERIFIER_assume(uint32_t v);

int myFunction(uint32_t a) {
  __VERIFIER_assume(a == 0);
  uint32_t c = 0;
  while (a < 4) {
    c = c + a;
    a++;
  }
  __VERIFIER_assert(c == 6);
  return c;
}
