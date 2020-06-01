const int x  = 17;
const int y  = 11;

typedef struct pair_s {
  int xx;
  int yy;
} pair_t;

pair_t z  = {x, y};

int main() {
  return z.xx;
}
