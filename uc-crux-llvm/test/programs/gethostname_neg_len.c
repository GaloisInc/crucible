#include <stdlib.h>
#include <unistd.h>
char *gethostname_neg_len() {
  char *buf = malloc(64);
  gethostname(buf, -1);
  return buf;
}
