#include <crucible.h>
#define N 15

int main()
{
    int i;
    for (i = 0; i < N; i++) {
        int b = crucible_int32_t("b");
        if (b != 0) {
	  switch (b) {
	  case 1: break;
	  case 2: i++;
	  default:
	    return i;
	  }
        }
    }
    crucible_assert(i == N, __FILE__, __LINE__);

    return 0;
}
