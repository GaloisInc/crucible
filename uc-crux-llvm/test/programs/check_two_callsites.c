#include <limits.h>

int f(int x) __attribute__((noinline))  {
  return INT_MAX - 2 + x;
}

int g(int x) __attribute__((noinline))  {
  return f(0); // no problem
}

int h(int x) __attribute__((noinline))  {
  return f(3); // overflow!
}
