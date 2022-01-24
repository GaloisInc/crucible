#include <string.h>
int memset_void_ptr(void *ptr, size_t len) { return memset(ptr, 0, len); }
