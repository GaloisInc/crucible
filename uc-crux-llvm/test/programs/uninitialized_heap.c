#include <stdlib.h>
int dereferences_argument(int *ptr) __attribute__((noinline)) { return *ptr; }
int uninitialized_heap() {
  int *x = malloc(sizeof(int));
  return dereferences_argument(x);
}
