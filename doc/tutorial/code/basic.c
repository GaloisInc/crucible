#include <stdint.h>
uint32_t add(uint32_t x, uint32_t y) {
    return x + y;
}

uint32_t dbl(uint32_t x) {
    return add(x, x);
}
