struct ty {
  int field_1;
  char field_2[10];
};

char struct_with_array(struct ty* ptr) {
  return ptr->field_2[5];
}
