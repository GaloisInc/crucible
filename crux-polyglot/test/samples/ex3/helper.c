#include <stdint.h>

int8_t update_value(int8_t v1, int8_t v2) {
    if (v1 << 1 > v2)
        return (v1 << 3 * v2);
    return (v2 + v1) >> 1;
}
