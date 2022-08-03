#include <stdint.h>
#include <crucible.h>

int main() {
  uint8_t x = crucible_uint8_t("x");
  uint8_t inc = x + 1;
  check(inc > x);
  return 0;
}