#include <stdio.h>

void do_getchar(void) {
  if (getchar() == 'X') {
    puts("X!");
  }
}
