void writes_to_arg_conditional_ptr(int *ptr) {
  if (ptr != 0) {
    *ptr = 4;
  }
}
