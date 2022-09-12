#include "crucible.h"
#include <stdlib.h>

int main() {
    if (crucible_uint8_t("x") == 0) {
        abort();
    }
    if (crucible_uint8_t("y") == 0) {
        *(int*)&main = 1;
    }
}
