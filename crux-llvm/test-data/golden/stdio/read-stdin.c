#include <crucible.h>

#include <stdio.h>
#include <unistd.h>

char buffer[100] = {0};

int main() {
  int res = read(STDIN_FILENO, buffer, 4);
  check(res == 4);
  // We don't have strcmp or bcmp overrides, so we just do the check manually
  check(buffer[0] == 'e' && buffer[1] == 'x' && buffer[2] == 'i' && buffer[3] == 't');
}
