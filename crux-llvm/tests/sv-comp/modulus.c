extern void __VERIFIER_assume(int);
extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern unsigned int __VERIFIER_nondet_uint(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: __VERIFIER_error();
  }
  return;
}
/* https://graphics.stanford.edu/~seander/bithacks.html#ModulusDivisionEasy */
#include <assert.h>

int main()
{
    /* Compute modulus division by (1 << s) - 1 without a division operator */
    unsigned int n = __VERIFIER_nondet_uint();                      /* numerator */
    unsigned int s = __VERIFIER_nondet_uint();                /* s > 0 */
    unsigned int d;
    unsigned int m;                      /* n % d goes here. */
    __VERIFIER_assume(s < 32);
    d = (1 << s) - 1; /* so d is either 1, 3, 7, 15, 31, ...) */

    if (d > 0) {
        m = n;
        while (n > d) {
            m = 0;
            while (n > 0) {
                m += n & d;
                n = n >> s;
            }
            n = m;
        }
        /* Now m is a value from 0 to d, but since with modulus division
         * we want m to be 0 when it is d. */
        if (m == d) {
            m = 0;
        }

        __VERIFIER_assert(m == n % d);
    }

    return 0;
}
