int dereferences_argument(int *ptr) __attribute__((noinline)) { return *ptr; }
int uninitialized_stack() {
  int x[8];
  return dereferences_argument(x);
}
