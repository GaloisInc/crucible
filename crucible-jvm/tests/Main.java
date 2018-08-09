class Main {

    static String[] arr = { "a" , "b" };
    //static int[][] arr = { { 8 , 1, 2 } };

    static String str = "Hello world";

    public static int foo() {
	System.out.println(str);
	return 3;
    } 
    
    public static int simmain() {

	Integer x = Integer.valueOf(3);
	
	System.out.println("hello" + "world");

	System.out.print(4);
	System.out.print('a');
	System.out.print(true);
	
	foo();
	return 5;
    }

    public static void main (String[] args) {
	System.out.println(simmain());
    }
    
}
   
