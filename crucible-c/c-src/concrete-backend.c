#include <stdio.h>
#include <stdlib.h>
#include <crucible.h>
#include <crucible-model.h>

void crucible_assume(uint8_t x, const char* file, int line) {
  if (x) return;
  fprintf(stderr, "%s:%d: Violated assumption.\n", file, line);
  exit(1);
}

void crucible_assert(uint8_t x, const char* file, int line) {
  if (x) return;
  fprintf(stderr, "%s:%d: Assertion failed.\n", file, line);
  exit(2);
}

#define mk_crux_func(ty) \
  ty crucible_##ty  (const char *name) { \
    (void)(name); \
    static unsigned long i = 0; \
    if (i < crux_value_num(ty)) return crux_values(ty)[i++]; \
    return 0; \
  }

mk_crux_func(int8_t)
mk_crux_func(int16_t)
mk_crux_func(int32_t)
mk_crux_func(int64_t)


unsigned int __VERIFIER_nondet_uint (void) { return crucible_int32_t("x"); }
void __VERIFIER_assume(int x) { crucible_assume(x, "??", 0); }
void __VERIFIER_error(void) { crucible_assert(0, "??", 0); }


