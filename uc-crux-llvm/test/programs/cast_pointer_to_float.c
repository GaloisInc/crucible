#include <stdint.h>
#include <stdlib.h>
float cast_uintptr_t_to_float(uintptr_t ptr) __attribute__((noinline)) {
  return (float)ptr;
}
float cast_pointer_to_float(int x) {
  int *ptr = malloc(x*sizeof(int));
  return (uintptr_t)cast_uintptr_t_to_float(ptr);
}
