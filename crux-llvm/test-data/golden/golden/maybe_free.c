#include <crucible.h>
#include <stdlib.h>

int main() {
  unsigned int b = crucible_uint32_t("b");
  int *p = malloc(sizeof(int));
  *p = b;
  if (b) {
    printf("%d\n", *p); // prevent optimizing everything away
    free(p);
  }
  return b;
}
