#include <stdlib.h>
void not_double_free(int *ptr, int x) {
  if (x % 2 == 0) {
    printf("even!\n"); // needed to prevent Clang from optimizing away the if/else
    free(ptr);
  }
  if ((x + 1) % 2 == 0) {
    free(ptr);
  }
}
