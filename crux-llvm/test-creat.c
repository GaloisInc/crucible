#include <fcntl.h>
#include <unistd.h>
#include <stdint.h>
#include <crucible.h>

int main() {
  // Test 1: Basic file creation with creat
  int fd = creat("/tmp/newfile.txt", 0644);
  check(fd >= 0);  // Should succeed

  // Write some data
  const char *msg = "test";
  ssize_t written = write(fd, msg, 4);
  check(written == 4);

  close(fd);

  return 0;
}
