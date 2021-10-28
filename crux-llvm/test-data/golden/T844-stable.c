#include <stdlib.h>

int main() {
  int x;
  if (x && !x) {
    abort();
  }

  return 0;
}
