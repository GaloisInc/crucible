#include <string.h>
int do_memset(void *ptr) __attribute__((noinline)) { memset(ptr, 0, 8); }
int memset_func_ptr() { return do_memset((void *)(&do_memset)); }
