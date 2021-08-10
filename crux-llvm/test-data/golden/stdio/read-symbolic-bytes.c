#include <crucible.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

uint8_t buffer[100] = {0};

int main() {
  int fd = open("/dev/urandom", O_RDONLY);
  check(fd > 0);
  int res = read(fd, buffer, 1);
  check(res == 1);
  // We should get the first character since this file exists
  uint32_t value = buffer[0];
  check(value < (uint32_t)256);
  for(int i = 0; i < 256; ++i) {
    check(value == i);
  }
}
