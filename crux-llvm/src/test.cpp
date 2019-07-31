
extern "C" {
  void crucible_ltl(unsigned char x, const char * file, int line);
  void crucible_assert(unsigned char x, const char * file, int line);
  int crucible_int32_t(const char *name);
}
//void A () {} unitRepr type
int A () {return 7;}// llvm pointer 32 type
//char A () {return 'a';} llvm pointer 8 type

//breaks things
/*typedef struct dummy{
  int x;
  char y;
} dummy;

dummy A() {
  dummy d;
  d.x = 7;
  d.y = 'a';
  return d;
  }*/
		
void B() {}

void C() {}
int main() {
  
  //crucible_ltl('x', __FILE__, __LINE__);
  int x = crucible_int32_t("x");
  if (x){
    B();
    A();
    //C();
  }
  else{
    A();
    B();
    //C();
    //C();
  }

}

