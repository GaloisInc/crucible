// A regression test for #1177. With Clang 12.0.0 or later, the `reduce_*`
// functions below will compile to uses of `llvm.vector.reduce.*` intrinsics
// with -O2, so this test checks that crucible-llvm's semantics for each of the
// `llvm.vector.reduce.*` intrinsics behave as expected.
#include <crucible.h>
#include <stddef.h>
#include <stdint.h>

uint32_t add(uint32_t x, uint32_t y) {
  return x + y;
}

uint32_t mul(uint32_t x, uint32_t y) {
  return x * y;
}

uint32_t and(uint32_t x, uint32_t y) {
  return x & y;
}

uint32_t or(uint32_t x, uint32_t y) {
  return x | y;
}

uint32_t xor(uint32_t x, uint32_t y) {
  return x ^ y;
}

uint32_t umin(uint32_t x, uint32_t y) {
  return (x < y) ? x : y;
}

uint32_t umax(uint32_t x, uint32_t y) {
  return (x > y) ? x : y;
}

#define REDUCE_OP_UNSIGNED(op, identity)                                        \
uint32_t __attribute__((noinline)) reduce_##op(const uint8_t* in, size_t len) { \
  uint32_t x = identity;                                                        \
                                                                                \
  for (size_t i = 0; i < len; i++) {                                            \
    x = op(x, in[i]);                                                           \
  }                                                                             \
                                                                                \
  return x;                                                                     \
}

REDUCE_OP_UNSIGNED(add, 0)
REDUCE_OP_UNSIGNED(mul, 1)
REDUCE_OP_UNSIGNED(and, -1)
REDUCE_OP_UNSIGNED(or, 0)
REDUCE_OP_UNSIGNED(xor, 0)
REDUCE_OP_UNSIGNED(umin, UINT32_MAX)
REDUCE_OP_UNSIGNED(umax, 0)

int32_t smin(int32_t x, int32_t y) {
  return (x < y) ? x : y;
}

int32_t smax(int32_t x, int32_t y) {
  return (x > y) ? x : y;
}

#define REDUCE_OP_SIGNED(op, identity)                                        \
int32_t __attribute__((noinline)) reduce_##op(const int8_t* in, size_t len) { \
  int32_t x = identity;                                                       \
                                                                              \
  for (size_t i = 0; i < len; i++) {                                          \
    x = op(x, in[i]);                                                         \
  }                                                                           \
                                                                              \
  return x;                                                                   \
}

REDUCE_OP_SIGNED(smin, INT32_MAX)
REDUCE_OP_SIGNED(smax, INT32_MIN)

int main(void) {
  const uint8_t unsigned_in1[8] = {0, 1, 2, 3, 4, 5, 6, 7};
  const uint8_t unsigned_in2[8] = {1, 2, 3, 4, 5, 6, 7, 8};
  const uint8_t unsigned_in3[8] = {5, 5, 5, 5, 4, 5, 5, 5};
  check(reduce_add(unsigned_in1, 8) == 28);
  check(reduce_mul(unsigned_in2, 8) == 40320);
  check(reduce_and(unsigned_in3, 8) == 4);
  check(reduce_or(unsigned_in2, 8) == 15);
  check(reduce_xor(unsigned_in2, 8) == 8);
  check(reduce_umin(unsigned_in3, 8) == 4);
  check(reduce_umax(unsigned_in1, 8) == 7);

  const int8_t signed_in[8] = {-3, -2, -1, 0, 1, 2, 3, 4};
  check(reduce_smin(signed_in, 8) == -3);
  check(reduce_smax(signed_in, 8) == 4);
  return 0;
}
