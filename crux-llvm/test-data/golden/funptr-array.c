/* See https://github.com/GaloisInc/crucible/issues/10 */

#include <crucible.h>

typedef int int_function(int);

int succ(int x) { return x+1; }
int pred(int x) { return x-1; }

int mytestfunction(int i, int j) {
    int_function *funs[] = { succ, pred };
    return funs[i](j);
}

int main() {
    int arg = __VERIFIER_nondet_int();
    int v   = __VERIFIER_nondet_int();
    int r;
    assuming(arg >= 0 && arg <= 1);
    r = mytestfunction(arg, v);
    check (r == v + 1);
    return 0;
}
