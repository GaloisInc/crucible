#include <stdlib.h>
void free_with_offset(int *ptr, int x) {
  free(ptr + x);
}
