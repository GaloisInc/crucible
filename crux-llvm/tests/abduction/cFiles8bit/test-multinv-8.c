#include <stdint.h>
#include <crucible.h>

int main() {
  int8_t x = crucible_int8_t("x");
  int8_t y = crucible_int8_t("y");
  int8_t prod = x * y;
  check(prod == 0);
  return 0;
}