#include <stdlib.h>
#include <string.h>

#include "crucible.h"

int* mk() {
  char* x = (int*) (malloc( 2*sizeof(int) + 2 ));
  char i = crucible_uint8_t( "i" );

  int* y = (int*) (x+2);

  assuming (i < 2u);

  y[i] = 42;

  return ((int*) x);
}

int main() {
  int* x = mk();
  //  int y = *x;
  //check( y < 100 );

  int y = *(x+1);
  check( y < 100 );
}
