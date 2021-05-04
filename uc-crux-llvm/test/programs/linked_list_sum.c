struct list {
  unsigned int head; // avoid signed wrapping by using unsigned int
  struct list *tail;
};
int linked_list_sum(struct list *l) {
  int total = l->head;
  struct list *next = l->tail;
  while (next != 0) {
    total += next->head;
    next = next->tail;
  }
}

