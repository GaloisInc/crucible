#include <fcntl.h>
#include <unistd.h>
#include <crucible.h>

int main() {
  // Test: Open with O_CREAT flag
  int fd = open("/tmp/created.txt", O_CREAT | O_WRONLY, 0644);
  check(fd >= 0);  // Should succeed

  // Write some data
  const char *data = "data";
  ssize_t written = write(fd, data, 4);
  check(written == 4);

  close(fd);

  return 0;
}
