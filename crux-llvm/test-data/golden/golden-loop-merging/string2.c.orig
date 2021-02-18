#include <crucible.h>

int string_length(const char* str) {
  int len = 0;
  int i = 0;
  while(str[i] != '\0') {
    i++;
    len++;
  }

  return len;
}

int main() {
  const char* str = crucible_string("x", 5);
  assuming(str[0] > 5 && str[0] < 20);
  assuming(str[1] > 5 && str[1] < 10);
  assuming(str[3] == 0);
  check(str[0] + str[1] > 5);
  check(string_length(str) <= 4);
  return 0;
}
