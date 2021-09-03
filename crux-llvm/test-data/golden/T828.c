#include <stdlib.h>

double const arr[2] = { -42, 42 };

int main() {
  if (arr[1] < 0) {
    abort();
  }
  return 0;
}
