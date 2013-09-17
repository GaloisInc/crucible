class Arrays {
    void clear(int a[]) {
        for(int i = 0; i < a.length; i++) a[i] = 0;
    }

    void copy(int a[], int b[]) {
        for(int i = 0; i < a.length; i++) b[i] = a[i];
    }
}
