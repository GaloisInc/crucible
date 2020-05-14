#include <stdbool.h>
#include <stdint.h>

void __VERIFIER_assert(uint32_t v);
void __VERIFIER_assume(uint32_t v);

uint32_t global = 1;

int myFunction(uint32_t argument) {
  // argument is in [0..5]
  __VERIFIER_assume(0 <= argument && argument <= 5);
  uint32_t local = 2;
  while (argument < 3) {
    local = local + global;
    argument++;
  }
  global = 1234;
  // local was incremented at most 3 times
  __VERIFIER_assert(argument >= 2 && 2 <= local && local <= 5);
  // global = 1234; // to check for proper handling of globals permanence and modification
  return global;
}
