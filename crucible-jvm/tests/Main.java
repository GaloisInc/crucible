class A {
    public String x = "A";
    public String m() {
	return x;
    }
    
}

class B extends A {
    public String y = "D";
    public String m() {
	x = "B";
	return x;
    }
}    

class Main {
    
    public static void main (String[] args) {
	B b = new B();
	b.m();
	((A)b).x = "C";
	System.out.println(b.x);
	b.y = "E";
	System.out.println(b.y);
    }
    
}
