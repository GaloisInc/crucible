struct list1 {
  unsigned int head; // avoid signed wrapping by using unsigned int
  struct list2 *tail;
};
struct list2 {
  unsigned int head;
  struct list1 *tail;
};
int mutually_recursive_linked_list_sum(struct list1 *l) {
  int total = l->head;
  struct list2 *next2 = l->tail;
  struct list1 *next1 = 0;
  while (next1 != 0 || next2 != 0) {
    if (next1 != 0) {
      total += next1->head;
      next2 = next1->tail;
      next1 = 0;
    }
    if (next2 != 0) {
      total += next2->head;
      next1 = next2->tail;
      next2 = 0;
    }
  }
  return total;
}
