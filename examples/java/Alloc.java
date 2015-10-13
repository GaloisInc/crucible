class Alloc {
    void alloc(int[] dst, int[] src) {
        int[] tmp = new int[src.length];
        int i;
        for(i = 0; i < src.length; i++) {
            tmp[i] = src[i];
        }
        for(i = 0; i < src.length; i++) {
            dst[i] = tmp[i];
        }
    }
}
