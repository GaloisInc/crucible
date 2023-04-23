#include <stdlib.h>
void free_if_even(int *ptr, int x) {
  if (x % 2 == 0) {
    free(ptr);
  }
}

void free_if_multiple_of_three(int *ptr, int x) {
  if (x % 3 == 0) {
    free(ptr);
  }
}

void double_free(int* ptr, int x) {
  free_if_even(ptr, x);
  free_if_multiple_of_three(ptr, x);  // bug: double free if x % 6 == 0
}
