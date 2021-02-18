#include <crucible.h>
#define N 8

int main()
{
    int i;
    for (i = 1; i <= N; i++) {
      int i0 = i;
      for (int j = 1; j <= i0; j++) {
        int b = crucible_int32_t("b");
        switch (b) {
	  case 1: break;
	  case 2: i++; break;
	  default:
	    return 0;
	}
      }
    }
    crucible_assert(i <= 16, __FILE__, __LINE__);

    return 0;
}
