#include <stdlib.h>
#include <crucible.h>

void __attribute__((noinline)) do_free(int *p) {
  free(p);
}

int main() {
  unsigned int b = crucible_uint32_t("b");
  int *p = malloc(sizeof(int));
  *p = b;
  if (b) {
    printf("%d\n", *p); // prevent optimizing everything away
    do_free(p);
  }
  free(p);
  return b;
}
