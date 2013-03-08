/* $Id: TestJava.java,v 1.1.1.1 2004/09/07 15:06:32 uid523 Exp $ */
import java.io.*;
public class TestJava {
  public static void main(String args[]) {
          String s = System.getProperty("java.specification.version");
          float d = Float.parseFloat(s);
	  // System.out.println(s);
          if (d<1.4) { 
            System.err.println(
    "Java "+s+" "+"is found. For \"jsim\" is needed: java 5.0 or higher"
            );
            System.exit(1);
            }
          System.exit(0);
          }
  }
