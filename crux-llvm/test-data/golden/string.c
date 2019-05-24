#include <crucible.h>

int main() {
  const char* str = crucible_string("x", 5);
  assuming(str[0] > 5 && str[0] < 20);
  assuming(str[1] > 5 && str[1] < 10);
  check(str[0] + str[1] > 5);
  return 0;
}
