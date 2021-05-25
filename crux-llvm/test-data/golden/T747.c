#include <crucible.h>
#include <stdint.h>

void __VERIFIER_assert(int cond);
void __VERIFIER_assume(int cond);
char __VERIFIER_nondet_char();

int main() {
  int8_t x = __VERIFIER_nondet_char();
  __VERIFIER_assume(x == x+0);
  __VERIFIER_assert(x == x+1);
  return 0;
}
