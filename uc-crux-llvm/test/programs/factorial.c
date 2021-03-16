unsigned int factorial(unsigned int x) {
  if (x == 0) {
    return 1;
  }
  return x * factorial(x - 1);
}
