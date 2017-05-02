import java.util.Scanner;

public class Wrapper {

    public static void main(String[] args){
	int i;
 	System.out.println("Addition de deux entiers 5 et 10 : ");
        i = MyClass.addition(5,10);
	System.out.println("resultat de la fonction addition: "+ i);
	System.out.println("Addition de deux entiers 5 et -10 : ");
        i = MyClass.addition(5,-10);
        System.out.println("resultat de la fonction addition: "+ i);
        System.out.println("Est-ce que 2 = 3 ?");
        i = MyClass.isEqual(2,3);
        if(i == 1) {
	     System.out.println("C'est vrai.");	
	}
        else {
	    System.out.println("C'est faux.");	
        }

    }

}
