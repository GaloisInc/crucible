#include <stdint.h>
#include <crucible.h>


int8_t f(int8_t x) {
  return x + 1;
}


void test_f(void) {
  forall(int8_t,x);

  assuming(x < 100);
  check(f(x) <= 100);
}


