#include <assert.h>
#include <crucible.h>
#include <stdint.h>
#include <stdlib.h>

extern void __CPROVER_assert(int32_t, const char *);

int main() {
  if (crucible_int8_t("test_abort")) {
    abort();
  } else if (crucible_int8_t("test_exit")) {
    exit(1);
#if defined(__APPLE__)
    __assert_rtn("0", "T785b.c", 15, "__assert_rtn");
#else
    __assert_fail("0", "T785b.c", 17, "__assert_fail");
#endif
  } else if (crucible_int8_t("test_crucible_assert")) {
    crucible_assert(0, "T785b.c", 20);
  } else if (crucible_int8_t("test_CPROVER_assert")) {
    __CPROVER_assert(0, "__CPROVER_assert");
  }

  return 0;
}
