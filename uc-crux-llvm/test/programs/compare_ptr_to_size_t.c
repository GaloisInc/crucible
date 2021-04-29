#include <stddef.h>
size_t compare(size_t x, size_t y) __attribute__((noinline)) { return x < y; }
size_t compare_ptr_to_size_t() {
  size_t x;
  return compare((size_t)&x, 7);
}
