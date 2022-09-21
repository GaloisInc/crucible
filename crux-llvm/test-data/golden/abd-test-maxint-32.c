#include <stdint.h>
#include <crucible.h>

int main() {
  uint32_t x = crucible_uint32_t("x");
  check(x + 1 > x);
  return 0;
}