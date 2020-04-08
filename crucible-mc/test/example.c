#include <stdint.h>
//
// void __VERIFIER_assert(uint32_t v);
// void __VERIFIER_assume(uint32_t v);

int myFunction(uint32_t a, int32_t b) {
  return a + b;
  // uint32_t a = 0;
  // uint32_t b = 1000;
  // uint32_t c = 0;

  // while (a < b) {
  //   c = c + a;
  //   a++;
  // }

  // __VERIFIER_assert(c >= a * (a - 1) / 2);
}

// #include <stdint.h>
// void __VERIFIER_assert(uint32_t b);
//
// void f () {
//   __VERIFIER_assert(0);
// }
