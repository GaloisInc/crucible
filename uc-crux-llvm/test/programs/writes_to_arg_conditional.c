void writes_to_arg_conditional(int *ptr, int x) {
  if (x == 4) {
    *ptr = 4;
  }
}
