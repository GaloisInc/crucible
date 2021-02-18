#include <stdint.h>
#include <crucible.h>

#define N 15

int bad() {
  int i;
    for (i = 0; i < N; ++i) {
        uint8_t x = crucible_uint8_t("x");
        uint8_t y = crucible_uint8_t("y");
        // Two symbolic branches
        if (100 < x) {
            if (100 < y) {
                return N;
            }
	    i++;
        }
    }
    return i;
}

int main() {
    int i = bad();
    crucible_assert ((N <= i && i <= N + 1), __FILE__, __LINE__);
}
