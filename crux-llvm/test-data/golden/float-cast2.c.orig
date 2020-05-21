#include <stdint.h>

float __VERIFIER_nondet_float(void);
void crucible_print_uint32( uint32_t x );

union fb {
  float f;
  uint8_t b[4];
};

int main() {
  union fb u;
  float f = __VERIFIER_nondet_float();
  u.f = f;

  union fb u2;

  u2.b[0] = u.b[0];
  u2.b[1] = u.b[1];
  u2.b[2] = u.b[2];
  u2.b[3] = u.b[3];

  crucible_print_uint32( u.f == u2.f );

  return 0;
}
