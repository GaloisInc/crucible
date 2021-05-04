#include <stdio.h>
void is() __attribute__((noinline)) { printf("is!\n"); }
void not() __attribute__((noinline)) { printf("not!\n"); }
int branch(int x, int y) {
  if (x == 2 && y == 4) {
    is();
  } else {
    not();
  }
  return 0;
}
