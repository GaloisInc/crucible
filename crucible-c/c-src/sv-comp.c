#include <sv-comp.h>
#include <stdio.h>
#include <stdlib.h>

void __VERIFIER_assume(int x) {
  if (x) return;
  fprintf(stderr, "An assumption was violated.\n");
  exit(1);
}

void __VERIFIER_error(void) {
  fprintf(stderr, "The vierifier encountered an error.");
  exit(2);
}


extern const size_t crucible_values_number_int32_t;
extern const int8_t crucible_values_int32_t [];

unsigned int __VERIFIER_nondet_uint (void) {
  static unsigned long i = 0;
  if (i < crucible_values_number_int32_t)
      return (unsigned int) crucible_values_int32_t[i++];
  return 0; // XXX: shouldn't happen
}

