unsigned int lots_of_loops(unsigned int x, unsigned int y) {
  unsigned int ret = x;
  for (unsigned int i = 0; i < (1 << 16); i++) {
    for (unsigned int j = 0; j < (1 << 16); j++) {
      for (unsigned int k = 0; k < (1 << 16); k++) {
        ret += y + (k / x);
      }
    }
  }
  return ret;
}
