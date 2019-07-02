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
  check(str[0] + str[1] > 5);
  // Note that crucible knows from the declaration that the string
  // length is for only 5 characters, so the following check is
  // trivially discharged and therefore crucible only reports
  // successfully proving one goal (the one above).  See string2.c for
  // a version that must prove both goals.
  check(string_length(str) <= 5);
  return 0;
}
