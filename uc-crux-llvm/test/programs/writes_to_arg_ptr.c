void writes_to_arg_ptr(int **ptrptr, int* ptr) {
  if (ptr != 0) {
    **ptrptr = 4;
  }
}
