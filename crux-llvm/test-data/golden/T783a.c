#include <stdlib.h>

struct s {
  unsigned int a;
  unsigned int b;
};

int f() {
  struct s *ss = malloc(sizeof(struct s));
  ss->b += 1;
  return ss->b;
}

int main() {
  return f();
}
