#include <string.h>
char str[] = "str";
int read_global_neg_offset_strlen() {
  return strlen(str - 1);
}
