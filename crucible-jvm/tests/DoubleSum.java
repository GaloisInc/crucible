public class DoubleSum
{
    // java claims that this will pass,
    // but it fails with crucible-jvm for some reason
    public static void main(String[] args)
    {
	float i2 = 2;
	float sum = ((float)3.4 + i2);
	System.out.println(sum);

	if (sum != 5.4) {
	    System.out.println("FAIL");
	}
	else {
	    System.out.println("PASS");
      }	
    }
    
 
}
