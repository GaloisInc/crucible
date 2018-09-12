
class A {
    int z = 0;
}

public class Main
{    
    public static void main(String[] args)
    {
	A[] x = { new A() };

	Object y = x;

	Object[] z = (A[])y;

	System.out.println(z[0]);

	
    }
    
 
}
