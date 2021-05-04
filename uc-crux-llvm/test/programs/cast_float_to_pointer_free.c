#include <stdint.h>
#include <stdlib.h>
uintptr_t cast_float_to_uintptr_t(float f) __attribute__((noinline)) {
  return (uintptr_t)f;
}
void cast_float_to_pointer_free(float x) {
  free((void *)cast_float_to_uintptr_t(x));
}
