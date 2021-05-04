int call_function_pointer(int(*fun_ptr)()) {
  return fun_ptr();
}

