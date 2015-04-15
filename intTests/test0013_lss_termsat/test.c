#include <inttypes.h>
#include <stdint.h>
#include <sym-api.h>
#include <stdio.h>
#include <stdlib.h>

int main()
{
  uint8_t x = lss_fresh_uint8(0);
  uint8_t y = lss_fresh_uint8(0);
  if (2 * x != x + x) {
    while (1) ;
  } else {
    return 0;
  }
}
