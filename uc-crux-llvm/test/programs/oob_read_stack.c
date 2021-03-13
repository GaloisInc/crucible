int dereferences_argument_16(int *ptr) __attribute__((noinline)) { return ptr[16]; }
int oob_read_stack() {
  int x[8];
  return dereferences_argument_16(x);
}
