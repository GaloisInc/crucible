#include <stdio.h>
#include <stdlib.h>
#include <crucible.h>

void crucible_assume(uint8_t x, const char* file, int line) {
  if (x) return;
  fprintf(stderr, "%s:%d: Violated assumption.\n", file, line);
  exit(1);
}

void crucible_assert(uint8_t x, const char* file, int line) {
  if (x) return;
  fprintf(stderr, "%s:%d: Assertion failed.\n", file, line);
  exit(2);
}


extern const size_t crucible_values_number_int8_t;
extern const int8_t crucible_values_int8_t [];
extern void (*crucible_counter_example_function)(void);

int8_t  crucible_int8_t  (const char *name) {
  (void)(name); // unused
  static unsigned long i = 0;
  if (i < crucible_values_number_int8_t) return crucible_values_int8_t[i++];
  return 0; // XXX: shouldn't happen
}

int main(int argc, char *argv[]) {
  (void)(argc);
  (void)(argv);
  crucible_counter_example_function();
  return 0;
}
