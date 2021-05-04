#include <stdlib.h>
void free_if_even(int *ptr, int x) {
  if (x % 2 == 0) {
    free(ptr);
  }
}

void free_if_odd(int *ptr, int x) {
  if ((x + 1) % 2 == 0) {
    free(ptr);
  }
}

void not_double_free(int *ptr, int x) {
  free_if_even(ptr, x);
  free_if_odd(ptr, x); // safe: x can't be both even and odd
}
