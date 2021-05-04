#include <stdlib.h>
void use_after_free(int *ptr, int x, int y) {
  if (x % 2 == 0) {
    free(ptr);
  }
  if (y % 2 == 0) {
    *ptr = 4;
  }
}
