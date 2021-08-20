/* see https://graphics.stanford.edu/~seander/bithacks.html#ParityNaive */
#include <assert.h>

extern unsigned int __VERIFIER_nondet_uint(void);
void __VERIFIER_assert(int cond) {
  if (!(cond)) {
    ERROR: assert(0);
  }
  return;
}

int main()
{
    unsigned int v = __VERIFIER_nondet_uint();
    unsigned int v1;
    unsigned int v2;
    char parity1;
    char parity2;

    /* naive parity */
    v1 = v;
    parity1 = (char)0;
    while (v1 != 0) {
        if (parity1 == (char)0) {
            parity1 = (char)1;
        } else {
            parity1 = (char)0;
        }
        v1 = v1 & (v1 - 1U);
    }

    /* smart parity */
    v2 = v;
    parity2 = (char)0;
    v2 = v2 ^ (v2 >> 1u);
    v2 = v2 ^ (v2 >> 2u);
    v2 = (v2 & 286331153U) * 286331153U; /* 286331153U == 0x11111111U */
    if (((v2 >> 28u) & 1u) == 0) {
        parity2 = (char)0;
    } else {
        parity2 = (char)1;
    }

    __VERIFIER_assert(parity1 == parity2);

    return 0;
}
