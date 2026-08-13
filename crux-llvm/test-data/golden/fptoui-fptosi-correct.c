#include <crucible.h>
#include <stdint.h>

int main(void) {
  double d1 = 1.5;
  check((uint64_t)d1 == 1);
  check((int64_t)d1 == 1);

  double d2 = -1.5;
  check((int64_t)d2 == -1);
  return 0;
}
