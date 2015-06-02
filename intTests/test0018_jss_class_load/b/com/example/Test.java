package com.example;

public class Test {
    static class Inner {}
    public static void main(String[] args) {
        Inner i = new Inner();
        OtherInSameFile o = new OtherInSameFile();
        org.example.Test t = new org.example.Test();
    }
}

class OtherInSameFile {}
