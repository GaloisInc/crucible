#include <crucible.h>

#include <stdio.h>
#include <unistd.h>

#define MSG "output\n"

int main() {
  // Write to an invalid (i.e., not opened) file descriptor, which should cause an error
  int res = write(100, MSG, sizeof(MSG));
  // Write should return an error because the FD is not allocated, so this assertion should succeed
  check(res == -1);
}
