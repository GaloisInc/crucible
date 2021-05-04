#include <stdlib.h>
const int x = 4;
void make_it_five(int *ptr) __attribute__((noinline)) { *ptr = 5; }

int write_const_global(int y) {
  make_it_five(&x);
  return y + x;
}
