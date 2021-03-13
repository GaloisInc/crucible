#include <stdio.h>
void loop_constant_big_bound_arg_start(int i) {
  for (; i < 8; i++) {
    printf("%d\n", i);
  }
}
