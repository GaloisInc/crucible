struct point {
  int x;
  int y;
};

void writes_to_arg_field(struct point *pt) {
  pt->x = 5;
}
