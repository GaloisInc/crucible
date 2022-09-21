#include <stdint.h>
#include <crucible.h>

int32_t f(int32_t x) {
  return x + 1;
}

int main() {
  int32_t x = crucible_int32_t("x");
  assuming(x < 100);
  check(f(x) < 100);
  return 0;
}