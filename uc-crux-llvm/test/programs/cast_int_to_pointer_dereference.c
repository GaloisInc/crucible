#include <stdint.h>
int cast_int_to_pointer_dereference(uintptr_t ptr) { return *((int *)(void *)ptr); }
