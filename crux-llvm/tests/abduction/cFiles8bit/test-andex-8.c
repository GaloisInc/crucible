#include <stdint.h>
#include <crucible.h>

int main() {
  uint8_t x = crucible_uint8_t("x");
  uint8_t y = crucible_uint8_t("y");
  assuming (x == 1);
  uint8_t conj = x & y;
  check(conj == 1);
  return 0;
}