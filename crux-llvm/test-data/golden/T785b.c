#include <assert.h>
#include <crucible.h>
#include <stdint.h>
#include <stdlib.h>

extern void __CPROVER_assert(int32_t, const char *);
extern void __VERIFIER_assert(int32_t);
extern void __VERIFIER_error();

int main() {
  if (crucible_int8_t("test_abort")) {
    abort();
  } else if (crucible_int8_t("test_exit")) {
    exit(1);
  } else if (crucible_int8_t("test_assert_fail")) {
    __assert_fail("0", "T785b.c", 16, "__assert_fail");
  } else if (crucible_int8_t("test_crucible_assert")) {
    crucible_assert(0, "T785b.c", 18);
  } else if (crucible_int8_t("test_CPROVER_assert")) {
    __CPROVER_assert(0, "__CPROVER_assert");
  } else if (crucible_int8_t("test_VERIFIER_assert")) {
    __VERIFIER_assert(0);
  } else if (crucible_int8_t("test_VERIFIER_error")) {
    __VERIFIER_error();
  }

  return 0;
}
