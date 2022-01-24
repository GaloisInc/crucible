int glob = 0;
int *minus_1(int *ptr) __attribute__((noinline)) { return ptr - 1; }
int read_global_neg_offset() {
  return *minus_1(&glob);
}
