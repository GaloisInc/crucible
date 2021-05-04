#include <unistd.h>
char *gethostname_arg_ptr_len(char *buf, int len) {
  gethostname(buf, len);
  return buf;
}
