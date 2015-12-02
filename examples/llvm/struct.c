typedef struct {
    int *x;
} s;

int add_indirect(s *o) {
    return (o->x)[0] + (o->x)[1];
}

void set_indirect(s *o) {
    (o->x)[0] = 0;
    (o->x)[1] = 0;
}

s *s_id(s *o) {
    return o;
}
