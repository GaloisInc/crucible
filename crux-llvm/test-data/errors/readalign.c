#include <stdlib.h>
#include <string.h>
#include <assert.h>

#include "crucible.h"

int mk() {
  char* x = (int*) (malloc( 2*sizeof(int) + 2 ));
  char i = crucible_uint8_t( "i" );

  x[0] = 0x01;
  x[1] = 0x23;
  x[2] = 0x45;
  x[3] = 0x67;
  x[4] = 0x89;
  x[5] = 0xab;
  x[6] = 0xcd;
  x[7] = 0xef;
  x[8] = 0x01;
  x[9] = 0x23;

  int* y = (int*) (x+2);

  assuming (i < 2u);

  return y[i];
}

int main() {
  int x = mk();
  assert( x < 100 );
}
