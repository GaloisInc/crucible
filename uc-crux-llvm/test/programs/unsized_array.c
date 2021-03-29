#include <stddef.h>

struct buffer {
  size_t len;
  char data[];
};

char unsized_array(struct buffer* p) {
  if (p->len > 8) {
    return p->data[6];
  }
  return 0;
}
