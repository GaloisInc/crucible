#include <stdint.h>
#include <crucible.h>

int main() {
  uint8_t x = crucible_uint8_t("x");
  uint8_t y = crucible_uint8_t("y");
  check(x & y == 1);
  return 0;
}