package com.galois.crucible;
import java.io.IOException;
import java.io.OutputStream;
import java.math.BigInteger;
import java.util.Iterator;

import com.galois.crucible.proto.Protos;

class Utils {
    private Utils() {}

    /*
    public static <T extends CrucibleSerializable>
    void writeIterableWithSize(OutputStream s,
                               int size,
                               Iterable<T> l) throws IOException {
        writeVaruint(s,size);
        Iterator<T> i = l.iterator();
        while (size > 0) {
            assert i.hasNext();
            T e = i.next();
            e.serialize(s);
            --size;
        }
    }

    public static <T extends CrucibleSerializable>
    void writeArray(OutputStream s, T[] l) throws IOException {
        int size = l.length;
        writeVaruint(s,size);
        for (int i = 0; i != size; ++i) {
            l[i].serialize(s);
        }
    }
    */

    static void writeString(OutputStream s, String v) throws IOException {
        s.write(v.getBytes("UTF-8"));
        s.write(0); // Add null terminator.
    }


    /**
     * Write a varint to stream.
     */
    static void writeVaruint(OutputStream s, long i) throws IOException {
        assert i >= 0;

        boolean c;
        do {
            // Get 7 low order bits;
            int next = (int) (i & 0x7f);
            i = i >>> 7;
            // Get whether we should continue
            c = i > 0;
            // Write byte
            s.write((c ? 0x80 : 0) | next);
        } while (c);
    }
}
