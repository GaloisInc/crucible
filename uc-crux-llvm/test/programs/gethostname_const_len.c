#include <stdlib.h>
#include <unistd.h>
char *gethostname_const_len() {
  char *buf = malloc(64);
  gethostname(buf, 64);
  return buf;
}
