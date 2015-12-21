class Return {
    public static int[] fill(int n) {
        int[] x = new int[5];
        for (int i = 0; i < 5; i++) x[i] = n;
        return x;
    }

    public static SimpleObj newSimple(int x, int y) {
        SimpleObj o = new SimpleObj();
        o.x = x;
        o.y = y;
        return o;
    }

    public static int[] fillwrap(int n) {
        return fill(n);
    }

    public static SimpleObj newSimpleWrap(int x, int y) {
        return newSimple(x, y);
    }

    public static int newSimpleWrap2(int x, int y) {
        SimpleObj o = newSimple(x, y);
        return 2;
    }

    public static void main(String[] args) {
        System.out.println(fill(22)[3]);
    }
}
