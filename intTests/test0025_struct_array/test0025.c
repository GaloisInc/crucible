#include <stdint.h>

struct S {
  uint32_t a[2];
  };

uint32_t sum(struct S *p) {
  return p->a[0] + p->a[1];
};
