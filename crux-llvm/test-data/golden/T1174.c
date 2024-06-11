#include <crucible.h>

__attribute__((noinline)) const char *F(int tag) {
  static const char *const table[] = {
    "A",
    "B",
    "C",
  };

  return table[tag];
}

int main() {
  check(F(0)[0] == 'A');
  check(F(1)[0] == 'B');
  check(F(2)[0] == 'C');
  return 0;
}
