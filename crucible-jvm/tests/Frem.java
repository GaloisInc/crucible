public class Frem {
    public static void main(String[] args) {
	float a = 1.5F; 
	float b = 0.9F;
	
	if (a % b == 0.6) {
	    System.out.println("PASS");
	} else {
	    System.out.println("FAIL");
	}
	System.out.print("\nwant: 0.6\n got: ");   System.out.println(a % b);  // frem

	double a1 = 1.5;
	double b1 = 0.9;
	
	if (a1 % b1 == 0.6) {
	    System.out.println("PASS");
	} else {
	    System.out.println("FAIL");
        }
	System.out.print("\nwant: 0.6\n got: ");   System.out.println(a1 % b1);  // drem
    }
}

/* 

crux-jvm produces:
``
FAIL

want: 0.6
 got: 0.6000000238418579
PASS

want: 0.6
 got: 0.6
``
but javac produces:
```
FAIL

want: 0.6
 got: 0.6
PASS

want: 0.6
 got: 0.6
```
*/
