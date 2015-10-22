typedef struct {
    int *x;
} s;

/*
int add_direct(s o) {
    return o.x + o.y;
}
*/

int add_indirect(s *o) {
    return (o->x)[0] + (o->x)[1];
}
