#include <stdint.h>

uint8_t f(uint8_t i) {
  int done = 0;
  while (!done){
    if (i % 8 == 0) done = 1;
    i += 5;
  }
  return i;
}
