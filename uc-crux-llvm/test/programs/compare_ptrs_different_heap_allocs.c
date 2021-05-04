#include <stdlib.h>
long compare(long x, long y) __attribute__((noinline)) { return x < y; }
long compare_ptrs_different_heap_allocs() {
  long *x = malloc(1);
  long *y = malloc(1);
  return compare((long)&x, (long)&y);
}
