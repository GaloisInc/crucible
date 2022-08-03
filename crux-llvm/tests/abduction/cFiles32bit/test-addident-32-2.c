#include <stdint.h>
#include <crucible.h>

int add(int32_t x, int32_t y) {
  int32_t sum = x + y;
  return sum;
}
int main() {
  int32_t x = crucible_int32_t("x");
  int32_t y = crucible_int32_t("y");
  check(add(x, y) == x);
  return 0;
}