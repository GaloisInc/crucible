#include <stdint.h>

float __VERIFIER_nondet_float(void);
void crucible_assert(uint8_t x, const char *file, int line);
#define check(e) crucible_assert(e, __FILE__, __LINE__)
void crucible_print_uint32( uint32_t x );

union fb {
  float f;
  uint8_t b[4];
};

int main() {
  union fb u;
  float f = __VERIFIER_nondet_float();
  u.f = f;

  crucible_print_uint32( u.b[0] );
  crucible_print_uint32( u.b[1] );
  crucible_print_uint32( u.b[2] );
  crucible_print_uint32( u.b[3] );

  return 0;
}
