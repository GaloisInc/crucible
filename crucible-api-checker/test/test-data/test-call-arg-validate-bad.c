
int crucible_int32_t(const char *name);

int A() {return 7;}
void B(int x) {}
int main() {
  int x = A();
  int y = 8;
  B(y);
}

