#include <stdint.h>
#include <stdio.h>
#include <crucible.h>

uint32_t gcd_depth(uint32_t depth, uint8_t a, uint8_t b) {
  printf("depth = %u\n", depth);
  if(b == 0)
    return depth;
  return gcd_depth(depth+1, b, a%b);
}


int main ( )
{
  uint8_t a = crucible_uint8_t( "a" );
  uint8_t b = crucible_uint8_t( "b" );

  uint32_t d = gcd_depth( 0, a, b);

  printf( "%d\n", d );

  // Should fail for some max-depth values, which
  // arise from consecutive fibonocci values
  check( d < 12 );

  return 0;
}
