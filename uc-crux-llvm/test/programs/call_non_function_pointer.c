#include <stddef.h>
#include <string.h>
typedef int (*fun_ptr_t)(void);
int call_function_pointer(fun_ptr_t fun_ptr) __attribute__((noinline)) {
  return fun_ptr();
}
int call_non_function_pointer(char x) {
  size_t arr[8];
  memset(arr, x, 8);
  return call_function_pointer((fun_ptr_t)arr);
}
