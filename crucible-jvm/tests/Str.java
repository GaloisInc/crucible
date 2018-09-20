class Str {
	public static void main (String args[]) {
		String str = "1234567890";
		StringBuffer a = new StringBuffer(str);
		a.insert(2, "abcd");
		System.out.println(a);
	}
}


/* Expected Output:
12abcd34567890
*/
