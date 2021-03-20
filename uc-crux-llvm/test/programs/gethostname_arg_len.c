#include <unistd.h>
char *gethostname_arg_len(int len) {
  char *buf = malloc(64);
  gethostname(buf, len);
  return buf;
}
