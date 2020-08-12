#include <stdio.h>
#include <crucible.h>

void crucible_dump_memory(void);

int f () {
  int arr[10];

  for( int i = 1; i <= 10; i++ ) {
    int x = crucible_uint16_t( "x" );
    arr[ x % i ] = i;
  }

  return arr[5];
}

int main () {
  int x = f();
  printf( "%d\n", x );
}
