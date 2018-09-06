
public class Main
{
    static int count = 0;
    
    public static void main(String[] args)
    {   
        int value = changeCount();
        int[] a = new int[2];
        
        a[count] = value;
                
        System.out.println(a[0] + ":" + a[1]);
    }
    
    public static int sum(int x, int y)
    {
        return x * 2 + y;
    }
    
    public static int changeCount()
    {
        return ++count; 
    }
}