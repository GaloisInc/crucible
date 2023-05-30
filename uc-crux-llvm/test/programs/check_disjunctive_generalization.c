#include <stdio.h>
// This function demonstrates a pretty fundamental limitation of UC-Crux-LLVM:
// Since y is dereferenced along *one* path through f, UC-Crux-LLVM will add a
// precondition that it's non-null, instead of a precondition that it's non-null
// when x is non-zero.
int f(int p, int x, int* y) __attribute__((noinline))  {
  printf("%i", p);  // Just to make sure there's something dynamic here
  if (x) {
    return *y;
  }
  return x;
}

int g(int x) __attribute__((noinline))  {
  // No problem
  return f(x, 0, 0);
}

int h(int x) __attribute__((noinline))  {
  // Null pointer dereference
  return f(x, 1, 0);
}
