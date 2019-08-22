
extern "C" {
  void crucible_ltl(unsigned char x, const char * file, int line);
  void crucible_assert(unsigned char x, const char * file, int line);
  int crucible_int32_t(const char *name);
}
void A () {}
void B() {}
void C() {}
int main() {
  int x = crucible_int32_t("x");
  if (x){
    B();   
  }
  else{
    A();
    B();
  }
  C();
}

