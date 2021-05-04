#include <stdlib.h>
int dereferences_argument_16(int *ptr) __attribute__((noinline)) {
  return ptr[16];
}
int oob_read_heap() {
  int *x = malloc(8*sizeof(int));
  return dereferences_argument_16(x);
}
