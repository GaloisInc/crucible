#include <stdint.h>
#include <crucible.h>

int main() {
  uint32_t x = crucible_uint32_t("x");
  uint32_t y = crucible_uint32_t("y");
  assuming (x == 1);
  check((x & y) == 1);
  return 0;
}