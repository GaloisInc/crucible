class FFS {
    static int ffs_ref(int word) {
        int i = 0;
        if(word == 0)
            return 0;
        for(int cnt = 0; cnt < 32; cnt++)
            if(((1 << i++) & word) != 0)
                return i;
        return 0;
    }

    static int ffs_imp(int i) {
        byte n = 1;
        if ((i & 0xffff) == 0) { n += 16; i >>= 16; }
        if ((i & 0x00ff) == 0) { n +=  8; i >>=  8; }
        if ((i & 0x000f) == 0) { n +=  4; i >>=  4; }
        if ((i & 0x0003) == 0) { n +=  2; i >>=  2; }
        if (i != 0) { return (n+((i+1) & 0x01)); } else { return 0; }
    }
}
