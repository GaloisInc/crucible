int main() {
  int x = 0;
  __builtin_prefetch(&x);
  return x;
}
