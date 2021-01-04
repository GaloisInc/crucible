#include <stdio.h>
#include <stdint.h>
#ifdef CRUCIBLE
#include <crucible.h>
#endif

extern int8_t update_value(int8_t v1, int8_t v2);

int8_t generate_value(int8_t seed) {
    int x;
    x = update_value(seed, seed * 3);
    if (x > 5)
        return 5;
    return x;
}

int8_t get_value(int8_t seed) {
    return generate_value(seed);
}

#ifdef CRUCIBLE
int main() {
    int8_t seed = crucible_int8_t("seed");
    assuming(seed < 10);
    check(get_value(seed) < 3);
    return 0;
}
#else
int main(int argc, char** argv) {
    int rval;
    rval = get_value(argc);
    printf("Value for %d is: %d\n", argc, rval);
    printf("Done\n");
}
#endif
