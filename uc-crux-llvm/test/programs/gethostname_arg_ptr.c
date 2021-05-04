#include <unistd.h>
char *gethostname_arg_ptr(char *buf) {
  gethostname(buf, 64);
  return buf;
}
