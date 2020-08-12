#include <stdint.h>
#include <stdio.h>
#include <crucible.h>

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

  uint8_t x = gcd( 0, a, b);

  printf( "%d\n", x );

  // Should fail for some values of "a" and "b" which are coprime
  check( x > 1 );

  return 0;
}
