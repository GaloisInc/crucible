#include <stdint.h>
#include <stdio.h>
#include <crucible.h>
/* CRUCIBLE clang_flags: -m64 -DTEST_FLAGS -Wall */
// CRUX CLANG_FLAGS: -Dmore_FLAGS -pthread

// This test exercises the path satisfiability option.
//
// The ouput should indicate that we only recursively call
// `gdc` up to depth = 12, which is the worst case for
// this algorithm on 8-bits.
//
// Without path-sat this should still terminate, but it
// takes 255 recursive calls instead for the bitvector
// abstract domain to determine the loop must terminate.
uint8_t gcd(uint32_t depth, uint8_t a, uint8_t b) {
  printf("depth = %u\n", depth);
  if(b == 0)
    return a;
  return gcd(depth+1, b, a%b);
}


int main ( )
{
  uint8_t a = crucible_uint8_t( "a" );
  uint8_t b = crucible_uint8_t( "b" );

#ifdef TEST_FLAGS
  printf("Starting gcd\n");
#endif

  uint8_t x = gcd( 0, a, b);

#ifdef more_FLAGS
  printf("Ended gcd run\n");
#endif

  printf( "%d\n", x );
  return 0;
}
