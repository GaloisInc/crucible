extern void clobbers_arg_void_ptr(void *x);
int calls_clobbers_arg_void_ptr(void) {
  int x;
  clobbers_arg_void_ptr(&x);
  return x;
}
