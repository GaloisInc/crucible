#include <stdlib.h>
void make_it_five(int *ptr) __attribute__((noinline)) { *ptr = 5; }
void write_to_null() { make_it_five(0); }
