package org.example;

public class Test {
    static class Inner {}
    public static void main(String[] args) {
        Inner i = new Inner();
        OtherInSameFile o = new OtherInSameFile();
    }
}

class OtherInSameFile {}
