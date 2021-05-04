#include <stdlib.h>

struct dict {
  char key;
  char value;
  struct dict *next;
};

void free_dict(struct dict **d) {
  struct dict *tmp;
  struct dict *next;
  if (*d == 0)
    return;
  tmp = *d;
  while (tmp) {
    next = tmp->next;
    free(tmp);
    tmp = next;
  }
  *d = 0;
}
