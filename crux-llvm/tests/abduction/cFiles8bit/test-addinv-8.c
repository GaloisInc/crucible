#include <stdint.h>
#include <crucible.h>

int main() {
  int8_t x = crucible_int8_t("x");
  int8_t y = crucible_int8_t("y");
  check(x + y == 0);
  return 0;
}