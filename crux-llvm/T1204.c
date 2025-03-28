__attribute__((noinline)) int foo(int x[2]) {
  return x[0];
}

int main(void) {
  int x[2] = { 0, 0 };
  return foo(x);
}
