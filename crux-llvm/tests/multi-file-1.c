#include <crucible.h>

void b(uint32_t);

int main() {
    uint32_t x = crucible_uint32_t("x");
    b(x);
    check (x == 5);
    return 0;
}
