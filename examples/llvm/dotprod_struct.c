#include <stdint.h>
#include <stdlib.h>
#include <sys/param.h>

typedef struct {
    uint32_t *elts;
    uint32_t size;
} vec_t;

// Computes the dot product of the smaller vector and the
// equivalently-sized prefix of the larger vector. This is the normal
// dot product if they're the same length.
uint32_t dotprod_struct(vec_t *x, vec_t *y) {
    uint32_t size = MIN(x->size, y->size);
    uint32_t res = 0;
    for(size_t i = 0; i < size; i++) {
        res += x->elts[i] * y->elts[i];
    }
    return res;
}

uint32_t dotprod_wrap(vec_t *x, vec_t *y) {
    return dotprod_struct(x, y);
}
