#include <stddef.h>
long compare(long x, long y) __attribute__((noinline)) { return x < y; }
long compare_ptrs_different_stack_allocs() {
  long x;
  long y;
  return compare((long)&x, (long)&y);
}
