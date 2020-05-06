#include <stdbool.h>
#include <stdint.h>

void __VERIFIER_assert(uint32_t v);
void __VERIFIER_assume(uint32_t v);

uint32_t global = 1;

int myFunction(uint32_t argument) {
  __VERIFIER_assume(argument <= 3);
  uint32_t local = 2;
  while (argument < 4) {
    local = local + global;
    argument++;
  }
  __VERIFIER_assert(local <= 5);
  return local;
}
