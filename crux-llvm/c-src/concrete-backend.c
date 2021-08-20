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
mk_crux_func(float)
mk_crux_func(double)

unsigned long  __VERIFIER_nondet_ulong (void)  { return crucible_int64_t("x"); }
long           __VERIFIER_nondet_long  (void)  { return crucible_int64_t("x"); }
unsigned int   __VERIFIER_nondet_uint (void)   { return crucible_int32_t("x"); }
int            __VERIFIER_nondet_int  (void)   { return crucible_int32_t("x"); }
unsigned short __VERIFIER_nondet_ushort (void) { return crucible_int16_t("x"); }
short          __VERIFIER_nondet_short (void)  { return crucible_int16_t("x"); }
unsigned char  __VERIFIER_nondet_uchar (void)  { return crucible_int8_t("x");  }
char           __VERIFIER_nondet_char (void)   { return crucible_int8_t("x");  }
int            __VERIFIER_nondet_bool (void)   { return crucible_int32_t("x"); }
float          __VERIFIER_nondet_float (void)  { return crucible_float("x");   }
double         __VERIFIER_nondet_double (void) { return crucible_double("x");  }


