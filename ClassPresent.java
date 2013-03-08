import java.lang.reflect.*;

class ClassPresent {

public static void main(String argv[]){
         Class c;
         if (argv.length==0) {
                 System.err.println("correct usage is with a single argument:");
                 System.err.println("java ClassPresent classname");
                 System.exit(1);
         }
         System.err.print("Class "+argv[0]+" is ");
         try {
                 c=Class.forName(argv[0]);
         } catch (java.lang.ClassNotFoundException e) {
                 System.err.println("missing");
                 System.exit(1);
         }
         System.err.println("present");
}
}

