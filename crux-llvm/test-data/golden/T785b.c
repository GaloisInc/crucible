#include <assert.h>
#include <crucible.h>
#include <stdint.h>
#include <stdlib.h>

extern void __CPROVER_assert(int32_t, const char *);

#if defined(__APPLE__)
// The expected output for this test case specifically mentions __assert_fail,
// so we need to call that in particular. __assert_fail isn't defined on macOS,
// so define a shim for it so that we can simulate it.
extern void __assert_fail(const char *, const char *, unsigned int, const char *);
#endif

int main() {
  if (crucible_int8_t("test_abort")) {
    abort();
  } else if (crucible_int8_t("test_exit")) {
    exit(1);
  } else if (crucible_int8_t("test_assert_fail")) {
    __assert_fail("0", "T785b.c", 21, "__assert_fail");
  } else if (crucible_int8_t("test_crucible_assert")) {
    crucible_assert(0, "T785b.c", 23);
  } else if (crucible_int8_t("test_CPROVER_assert")) {
    __CPROVER_assert(0, "__CPROVER_assert");
  }

  return 0;
}
