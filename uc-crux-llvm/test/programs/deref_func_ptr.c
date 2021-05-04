int deref_arg(void *ptr) __attribute__((noinline)) { return *(int*)ptr; }
int deref_func_ptr() { return deref_arg((void *)(&deref_arg)); }
