#include <stdlib.h>
#include <stdio.h>
#include <math.h>

#include <crucible.h>

int main() {
  double x = crucible_double( "x" );

  // should fail for NaN
  check( x == x );

  // should fail for INFINITY
  check( isnan(x) || x < INFINITY );

  // should fail for -INFINITY
  check( isnan(x) || -INFINITY < x );

  // should fail for -0.0
  check( x < 0 || x > 0 || !signbit(x) );

  // should fail for sufficently large/small x
  check( isnan(x) || isinf(x) || x+1 > x );

  // should fail for a denormal value
  check( isnan(x) || isinf(x) || x <= 0 || isnormal(x) );
}
