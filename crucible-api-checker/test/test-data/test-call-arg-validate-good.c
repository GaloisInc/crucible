
extern "C" {
  void crucible_ltl(unsigned char x, const char * file, int line);
  void crucible_assert(unsigned char x, const char * file, int line);
  int crucible_int32_t(const char *name);
}

int A() {return 7;}
void B(int x) {}
int main() {
  int x = A();
  B(x);
}

