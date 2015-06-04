#include <stdint.h>
#include "sym-api.h"

void test_case(uint8_t in, uint8_t* out) {
  switch( in ) {
  case 0:
    *out = 1;
    break;
  default:
    *out = 4;
  }
}

uint8_t test_case_wrapper(uint8_t x)
{
  uint8_t ret;
  test_case(x, &ret);
  return ret;
}
