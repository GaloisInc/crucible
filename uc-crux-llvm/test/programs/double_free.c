#include <stdlib.h>
void double_free(int* ptr, int x) {
  if (x % 2 == 0) {
    free(ptr);
  }
  if (x % 3 == 0) {
    free(ptr);
  }
}
