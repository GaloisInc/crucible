#include <crucible.h>

#include <stdio.h>
#include <unistd.h>

#define MSG "output\n"

int main() {
  int res = write(STDOUT_FILENO, MSG, sizeof(MSG));
  check(res == sizeof(MSG));
}
