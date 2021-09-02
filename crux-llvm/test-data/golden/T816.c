#include <stdlib.h>

int a = 42;

void f(int b) {
  a = b;
}

int main(int argc, char *argv[]) {
  f(argc);
  if (!a) {
    return 0;
  } else {
    abort();
  }
}
