#include <stdio.h>
#include <crucible.h>

int* f () {
  int x = 42;
  return &x;
}

int g( int* x, int* y ) {
  return (x == y);
}

int main () {
  int y;
  int* x = f();

  printf( "%d\n", g( x, &y) );
}
