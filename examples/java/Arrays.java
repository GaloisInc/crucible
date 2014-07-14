class Arrays {
    void unit(int a[]) {
        for(int i = 0; i < a.length; i++) a[i] = 0;
        a[0] = 1;
    }

    void copy(int a[], int b[]) {
        for(int i = 0; i < a.length; i++) b[i] = a[i];
    }

    void comp(int a[]) {
        unit(a);
    }
}
