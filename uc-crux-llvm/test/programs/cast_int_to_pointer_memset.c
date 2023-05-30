#include <stdint.h>
#include <string.h>
int *cast_int_to_pointer_memset(uintptr_t ptr) {
  return memset((char *)(void *)ptr, 0, 8);
}
