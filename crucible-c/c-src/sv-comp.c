/* NOTE: This file is baked into the executable.

   * If you change it, you need to recompile.
   * Since this is not a standard Haskell file, make sure that you *did*
     recompile after the change.
     (e.g., cabal 2.2.0.0 does not notice this dependency)
*/

#include <stdio.h>
#include <stdlib.h>
#include <stddef.h>

extern size_t  const crucible_values_number_int32_t;
extern int32_t const crucible_values_int32_t [];

unsigned int __VERIFIER_nondet_uint (void) {
  static size_t i = 0;
  if (i < crucible_values_number_int32_t)
      return (unsigned int) crucible_values_int32_t[i++];
  return 72; // XXX: shouldn't happen
}

void __VERIFIER_assume(int x) {
  if (x) return;
  fprintf(stderr, "An assumption was violated.\n");
  exit(1);
}

void __VERIFIER_error(void) {
  fprintf(stderr, "The verifier encountered an error.\n");
  exit(2);
}


