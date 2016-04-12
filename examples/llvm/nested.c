#include <stdint.h>

typedef struct s {
    uint32_t a;
    uint32_t b;
} s_t;

typedef struct t {
    uint32_t x;
    s_t n;
    uint32_t z;
} t_t;

uint32_t f(t_t *p) {
    return (p->n).b;
}
