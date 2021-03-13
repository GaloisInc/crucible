typedef struct point {
  int x;
  int y;
} point;

int deref_struct_field(point *pt) { return pt->x; }
