#include <crucible.h>

#include <stdio.h>
#include <unistd.h>

char buffer[100] = {0};

int main() {
  int res = close(STDIN_FILENO);
  check(res == 0);
  // This read should fail because we closed the file descriptor
  res = read(STDIN_FILENO, buffer, 4);
  check(res == -1);
}
