class ArrayField {
    int a[];
    void init(int x) {
        int[] na = new int[5];
        for(int i = 0; i < 5; i++) na[i] = x;
        a = na;
    }
}
