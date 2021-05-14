int N = 10;

int main() {
  int i;
  int j = 0;
  int a[N];

  for (i = 0; i < N; i++) {
    a[i] = 0;
  }

  for (i = 0; i < N; i++){
    if (a[i] == 0) {
      j++;
    }
  }

  return 0;
}
