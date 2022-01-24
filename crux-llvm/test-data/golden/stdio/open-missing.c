#include <crucible.h>

#include <sys/types.h>
#include <sys/stat.h>
#include <fcntl.h>
#include <stdio.h>
#include <unistd.h>

int main() {
  int fd = open("/etc/lsb_base", O_RDONLY);
  check(fd == -1);
}
