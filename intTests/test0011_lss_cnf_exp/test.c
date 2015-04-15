#include <inttypes.h>
#include <stdint.h>
#include <sym-api.h>
#include <stdio.h>
#include <stdlib.h>

uint8_t exp_ref(uint8_t x, uint8_t p) {
  uint8_t r = 1;
  while (p--) {
    r *= x;
  }
  return r;
}

uint8_t exp_opt(uint8_t x, uint8_t p) {
  uint8_t r = 1;
  for (; p; x *= x, p >>= 1) {
    if (p & 1) {
      r *= x;
    }
  }
  return r;
}

void test() {
  uint8_t x = 0;
  uint8_t p = 0;
  do {
    do {
      if (exp_ref(x,p) != exp_opt(x,p)) {
        printf("Counterexample: %i %i", x, p);
        exit(1);
      }
    } while (++p != 0);
  } while (++x != 0);
}

int main()
{
  //test();
  uint8_t x = lss_fresh_uint8(0);
  uint8_t y = lss_fresh_uint8(0);
  lss_write_cnf(exp_ref(x,y) != exp_opt(x,y), "tmp/exp.cnf");
  return 0;
}
