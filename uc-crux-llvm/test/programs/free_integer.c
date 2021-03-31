#include <stdlib.h>
void do_free(void *ptr) { free(ptr); }
void free_integer(float x) { do_free((void *)x); }
