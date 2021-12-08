extern void clobbers_arg(int *x);
int calls_clobbers_arg(void) {
  int x;
  clobbers_arg(&x);
  return x;
}
