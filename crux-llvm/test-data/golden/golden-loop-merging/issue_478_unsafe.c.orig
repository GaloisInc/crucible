#include <stdint.h>
#include <crucible.h>

#define N 30

/* int good() { */
/*     for (int i = 0; i < N; ++i) { */
/*         uint8_t x = crucible_uint8_t("x"); */
/*         // One symbolic branch */
/*         if (100 < x) { */
/*             return 1; */
/*         } */
/*     } */
/*     return 0; */
/* } */

int bad() {
  int i = 0;
    for (i = 0; i < N; ++i) {
        uint8_t x = crucible_uint8_t("x");
        uint8_t y = crucible_uint8_t("y");
        // Two symbolic branches
        if (100 < x) {
            if (100 < y) {
                return 1;
            }
	    i++;
        }
    }
    return i;
}

int main() {
    int i = bad();
    crucible_assert(i != N && i != N + 1, __FILE__, __LINE__);
}
