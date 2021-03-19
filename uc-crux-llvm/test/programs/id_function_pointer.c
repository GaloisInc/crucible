typedef int (*fun_ptr_t)(void);
fun_ptr_t id_function_pointer(fun_ptr_t ptr) { return ptr; }
