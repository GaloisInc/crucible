#include <stdint.h>
#include <crucible.h>

int main() {
  uint8_t x = crucible_uint8_t("x");
  check(x + 1 > x);
  return 0;
}
