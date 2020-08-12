#include <stdio.h>
#include <assert.h>

#include <crucible.h>

void crucible_dump_memory(void);

int f () {
  int arr[10];
  for( int i = 0; i < 10; i++ ) {
    arr[i] = i;
  }

  unsigned int len = crucible_uint32_t("len");
  assuming( len < 7*sizeof(int) );

  memcpy( &arr[0], &arr[3], len );

  return arr[0];
}

int main () {
  int x = f();
  printf( "%d\n", x );
  assert( x > 5 );
}
