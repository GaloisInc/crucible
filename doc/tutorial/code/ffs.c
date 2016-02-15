#include <stdint.h>

#ifdef RUN
#include <stdio.h>
typedef unsigned int uint32_t;
#endif

// returns the index of the first non-zero bit
uint32_t ffs_ref(uint32_t word) {
    int i = 0;
    if(!word)
        return 0;
    for(int cnt = 0; cnt < 32; cnt++)
        if(((1 << i++) & word) != 0)
            return i;
    return 0; // notreached
}

uint32_t ffs_imp(uint32_t i) {
    char n = 1;
    if (!(i & 0xffff)) { n += 16; i >>= 16; }
    if (!(i & 0x00ff)) { n += 8;  i >>= 8; }
    if (!(i & 0x000f)) { n += 4;  i >>= 4; }
    if (!(i & 0x0003)) { n += 2;  i >>= 2; }
    return (i) ? (n+((i+1) & 0x01)) : 0;
}

uint32_t ffs_imp_nobranch(uint32_t i) {
  char n = 1;
  int s1 = !(i & 0xffff) << 4;
  n += s1; i >>= s1;
  int s2 = !(i & 0x00ff) << 3;
  n += s2;  i >>= s2;
  int s3 = !(i & 0x000f) << 2;
  n += s3;  i >>= s3;
  int s4 = !(i & 0x0003) << 1;
  n += s4;  i >>= s4;
  // Still does have one branch...
  return (i) ? (n+((i+1) & 0x01)) : 0;
}

// and now a buggy one
uint32_t ffs_bug(uint32_t word) {
    // injected bug:
    if(word == 0x101010) return 4; // instead of 5
    return ffs_ref(word);
}

#ifdef RUN
int main(int argc, char **argv) {
    uint32_t t = 0x800000;
    printf("(imp, ref) 0x%x -> (0x%x, 0x%x)\n", t, ffs_imp(t), ffs_ref(t));
    t = 0x000002;
    printf("(imp, ref) 0x%x -> (0x%x, 0x%x)\n", t, ffs_imp(t), ffs_ref(t));
    t = 0x000008;
    printf("(imp, ref) 0x%x -> (0x%x, 0x%x)\n", t, ffs_imp(t), ffs_ref(t));
    t = 0x101010;
    printf("(bug, ref) 0x%x -> (0x%x, 0x%x)\n", t, ffs_bug(t), ffs_ref(t));
}
#endif
