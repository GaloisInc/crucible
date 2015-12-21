int add(int *x, int *y) {
    return *x + *y;
}

void clear(int a[10]) {
    for(int i = 0; i < 10; i++) {
        a[i] = 0;
    }
}

void copy(int a[10], int b[10]) {
    for(int i = 0; i < 10; i++) {
        a[i] = b[i];
    }
}
