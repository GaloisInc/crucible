#include <crucible.h>
#define N 7
#define M 7

int main()
{
    int i;
    for (i = 0; i < M; i++) {
        int b = crucible_int32_t("b");
        if (b != 0) {
	  switch (b) {
	  case 2: i++;
	  case 1: continue;
	  default:
	    return i;
	  }
	  break;
        }
    }

    for (int j = 0; j < N; j++) {
        int b = crucible_int32_t("b");
        if (b != 0) {
	  switch (b) {
	  case 2: i+=N;
	  case 1: break;
	  default:
	    return i;
	  }
        }
    }
    crucible_assert(0 <= i && i <= M+N+1, __FILE__, __LINE__);

    return 0;
}
