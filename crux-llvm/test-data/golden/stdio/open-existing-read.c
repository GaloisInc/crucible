#include <crucible.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

char buffer[100] = {0};

int main() {
  int fd = open("/etc/fstab", O_RDONLY);
  check(fd > 0);
  int res = read(fd, buffer, 1);
  check(res == 1);
  // We should get the first character since this file exists
  check(buffer[0] == '#');
}
