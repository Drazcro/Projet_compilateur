import java.util.Scanner;

public class Wrapper {

    public static void main(String[] args){
	int i;
 	System.out.println("Addition de deux entiers 5 et 10 : ");
        i = MyClass.addition(5,10);
	System.out.println("resultat de la fonction addition: "+ i);
	System.out.println("Addition de deux entiers 5 et -10 : ");
        i = MyClass.addition(5,-10);
        System.out.println("Resultat de la fonction addition: "+ i);
        System.out.println("Est-ce que 2 = 3 ?");
        i = MyClass.isEqual(2,3);
        if(i == 1) {
	     System.out.println("C'est vrai.");	
	}
        else {
	    System.out.println("C'est faux.");	
        }
        i = MyClass.zero(50);
	System.out.println("Resultat de la fonction zero sur 50: "+ i);
	 i = MyClass.zero(-50);
        System.out.println("Resultat de la fonction zero sur -50: "+ i);
	i = MyClass.increment(2);
 	System.out.println("Resultat de la fonction increment de 2: "+i);
        i = MyClass.isNatural(2);
        System.out.println("Resultat de la fonction isNatural de 2: ");
	if(i == 1) {
	     System.out.println("il est bien naturel.");	
	}
        else {
	    System.out.println("Il n'est pas naturel.");	
        }
        
    }

}
