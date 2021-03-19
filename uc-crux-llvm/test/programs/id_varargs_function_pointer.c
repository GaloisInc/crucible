typedef int (*fun_ptr_t)(int x, ...);
fun_ptr_t id_varargs_function_pointer(fun_ptr_t ptr) { return ptr; }
