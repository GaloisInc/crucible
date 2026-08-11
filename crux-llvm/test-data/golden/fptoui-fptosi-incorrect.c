#include <math.h>
#include <stdint.h>

int main(void) {
  double d1 = NAN;
  uint64_t u1 = (uint64_t)d1;
  int64_t i1 = (int64_t)d1;

  double d2 = -INFINITY;
  uint64_t u2 = (uint64_t)d2;
  int64_t i2 = (int64_t)d2;

  double d3 = INFINITY;
  uint64_t u3 = (uint64_t)d3;
  int64_t i3 = (int64_t)d3;
  return 0;
}
