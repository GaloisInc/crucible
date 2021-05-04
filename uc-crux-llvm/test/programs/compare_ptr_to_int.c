#include <stddef.h>
size_t compare(int x, int y) __attribute__((noinline)) { return x < y; }
size_t compare_ptr_to_int() {
  size_t x;
  return compare((size_t)&x, 7);
}
