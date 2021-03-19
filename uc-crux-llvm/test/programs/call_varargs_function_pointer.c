int call_varargs_function_pointer(int (*fun_ptr)(int x, ...)) {
  return fun_ptr(5, 6, 7);
}
