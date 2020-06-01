#include <stdint.h>

unsigned int __VERIFIER_nondet_uint(void);
void crucible_assert(uint8_t x, const char *file, int line);
#define check(e) crucible_assert(e, __FILE__, __LINE__)
void crucible_print_uint32( uint32_t x );

union fb {
  uint32_t u;
  uint8_t b[4];
};

int main() {
  union fb u;
  uint32_t x = __VERIFIER_nondet_uint();
  u.u = x;

  crucible_print_uint32( u.b[0] );
  crucible_print_uint32( u.b[1] );
  crucible_print_uint32( u.b[2] );
  crucible_print_uint32( u.b[3] );

  return 0;
}
