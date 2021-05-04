#include <stdlib.h>
struct list {
  unsigned int head;
  struct list *tail;
};
void free_linked_list(struct list *l) {
  struct list *tmp;
  struct list *next;
  if (l == 0)
    return;
  tmp = l;
  while (tmp) {
    next = tmp->tail;
    free(tmp);
    tmp = next;
  }
}
