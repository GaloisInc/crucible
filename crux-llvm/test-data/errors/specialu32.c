#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include <crucible.h>

int main() {
  uint32_t x = crucible_uint32_t( "x" );

  // should fail for MAXINT
  check( x+1 > x );

  // should fail for MININT
  check( x-1 < x );
}
