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

    public static void main(String[] args) {
        System.out.println(fill(22)[3]);
    }
}
