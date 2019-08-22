extern "C" {
  int crucible_int32_t(const char *name);
}
void A () {}
void B() {}
void C() {}
int main() {
  int x = crucible_int32_t("x");
  if (x){
    B();
    A();
   }
  else{
    A();
    B();
  }
  C();
}

