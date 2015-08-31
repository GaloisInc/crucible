#include <stdint.h>

uint32_t side_effect(uint32_t *a) {
  uint32_t v;
  v = *a;
  *a = 0;
  return v;
}

uint32_t foo(uint32_t x) {
  uint32_t b = x;
  side_effect(&b);
  return side_effect(&b);
}