#include <crucible.h>

#include <stdio.h>
#include <unistd.h>

// Read 256 bytes of concrete stdin and return their unsigned sum.
// With the ArrayFromFn representation, each arrayLookup beta-reduces
// a 256-way ITE tree; with ArrayMap it's O(log n) per lookup.

unsigned char buffer[256];

int main() {
  int n = read(STDIN_FILENO, buffer, 256);
  check(n == 256);

  unsigned int sum = 0;
  for (int i = 0; i < 256; i++) {
    sum += buffer[i];
  }

  // 0 + 1 + 2 + ... + 255 = 32640
  check(sum == 32640);
  return 0;
}
