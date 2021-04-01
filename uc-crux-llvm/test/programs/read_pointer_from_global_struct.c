struct foo {
  int *ptr;
};
struct foo glob;
int read_pointer_from_global_struct() { return *glob.ptr; }
